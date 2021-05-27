-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
{-# OPTIONS --rewriting #-}


open import Reflection
open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Data.Bool
open import Data.String renaming (_++_ to _++S_)
open import Data.List
open import Data.Empty
open import Function hiding (flip)

module Automation.utils.reflectionUtils where

pure = return

infix 30 _↦_

postulate  -- HIT
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i

{-# BUILTIN REWRITE _↦_ #-}



_<*>_ : ∀ {α β} {A : Set α} {B : Set β} → TC (A → B) → TC A → TC B
f <*> x =
  do f' ← f
     x' ← x
     return (f' x')

case!_of_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
case! x of f =
  do y ← x
     case y of f


{-- Generator for Recursion Principle --}

getConstructors : Name → TC (List Name)
getConstructors d =
  case! getDefinition d of λ
   { (data-type _ cs) → return cs
   ; (record-type c _) → return (c ∷ [])
   ; _ → typeError (strErr "Cannot get constructors of non-data or record type" ∷ nameErr d ∷ [])
   }


getParameters : Name → TC Nat
getParameters d =
  do data-type n _ ← (getDefinition d)
       where _ → return 0
     return n


isDefinition : Name → TC Bool
isDefinition d =
  case! getDefinition d of λ
   { (data-type _ cs) → return true
   ; (record-type c _) → return true
   ; _ → return false
   }

{--
map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
--}

checkTrue : List Bool → TC Bool
checkTrue [] = return false
checkTrue (true ∷ bs) = return true
checkTrue (false ∷ bs) = checkTrue bs

eq : Nat → Nat → Bool
eq zero    zero    = true
eq (suc m) (suc n) = eq m n
{-# CATCHALL #-}
eq _       _       = false

isMember : Nat → List Nat → TC Bool
isMember a [] = return false
isMember a (x ∷ xs) =
  if eq a x
    then return true
    else isMember a xs

_or_ : (b1 : Bool) → (b2 : Bool) → Bool
x or true = true
true or x = true
x or y = false

_and_ : (b1 : Bool) → (b2 : Bool) → Bool
true and true = true
false and x = false
x and false = false

notB : (b : Bool) → Bool
notB true = false
notB false = true

-- [_] : ∀ {a} {A : Set a} → A → List A
-- [ x ] = x ∷ []

_++L_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

_∷L_ : ∀ {a} {A : Set a} → List A → A → List A
xs ∷L x = xs ++L [ x ]

-- foldl : {A B : Set} -> (B -> A -> B) -> B -> List A -> B
-- foldl f z []        = z
-- foldl f z (x ∷ xs) = foldl f (f z x) xs

flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f x y = f y x

reverseTC : {A : Set} → List A → TC (List A)
reverseTC xs = return (foldl (flip _∷_) [] xs)

showNat : Nat → String
showNat zero = "Z1"
showNat (suc x) = "S (" ++S showNat x ++S ")"

takeTC : ∀ {a} {A : Set a} → Nat → List A → TC (List A)
takeTC zero    xs       = return []
takeTC (suc n) []       = return []
takeTC (suc n) (x ∷ xs) = bindTC (takeTC n xs)
                                 (λ xs' → return (x ∷ xs'))

{--
take1 : ∀ {a} {A : Set a} → ℕ → List A → (List A)
take1 zero    xs       = []
take1 (suc n) []       = []
take1 (suc n) (x ∷ xs) = x ∷ (take1 n xs)
--}

dropTC : ∀ {a} {A : Set a} → Nat → List A → TC (List A)
dropTC zero    xs       = return xs
dropTC (suc n) []       = return []
dropTC (suc n) (x ∷ xs) = bindTC (dropTC n xs) (λ xs' → return xs')

-- consArgs : Nat → (vis : List Bool) → Type → TC (List (Arg Pattern))
-- consArgs ref b (def qn ls) = return []
-- consArgs ref (b ∷ bs) (pi (arg info dom) (abs s cdom)) = bindTC (consArgs (suc ref) bs cdom)
--                                                                 (λ y → bindTC (return b) λ
--                                                                           { true → return (hArg (var {!!}) ∷ y) ;
--                                                                             false → return (vArg (var {!!}) ∷ y) })
-- consArgs ref b x = return (vArg (absurd {!!}) ∷ [])

getClauseVars : Nat → Nat → TC (List (Arg Pattern))
getClauseVars ref zero = return []
getClauseVars ref (suc x) = bindTC (getClauseVars (suc ref) x)
                                   (λ y → return (vArg (var ref) ∷ y))

getClauseVarsHid : Nat → Nat → TC (List (Arg Pattern))
getClauseVarsHid ref zero = return []
getClauseVarsHid ref (suc x) = bindTC (getClauseVarsHid (suc ref) x)
                                      (λ y → return (hArg (var ref) ∷ y))

getLength : ∀ {a} {A : Set a} → List A → TC Nat
getLength []       = return 0
getLength (x ∷ xs) = bindTC (getLength xs)
                            (λ y → return (1 + y))

getRef : ∀ {a} {A : Set a} → (ref : Nat) → List A → TC (List Nat)
getRef ref [] = return []
getRef ref (x ∷ xs) = bindTC (getRef (suc ref) xs)
                              (λ y → return (ref ∷ y))

checkCdmR : Name → Type → TC Bool
checkCdmR R (def ty y) = return (primQNameEquality R ty)
checkCdmR R (pi (arg info t1) (abs s t2)) = bindTC (checkCdmR R t2) (λ y → return y)
checkCdmR R y = return false

getListElement : (n : Nat) → List Nat → TC Nat
getListElement 0 (x ∷ xs) = return x
getListElement (suc n) (x ∷ xs) = bindTC (getListElement n xs)
                                         (λ y → return y)
getListElement x y = return x

_$_<or>_ : {A : Set} → Bool → A → A → TC A
b $ x <or> y = return (if b then x else y)

generateRef : (l : Nat) → TC (List Nat)
generateRef 0 = return []
generateRef (suc x) = bindTC (generateRef x)
                             (λ y → return (x ∷ y))

generateRef1 : (l : Nat) → (List Nat)
generateRef1 0 = []
generateRef1 (suc x) = x ∷ (generateRef1 x)

generateMapRef : (f : Nat) → (fargs : List (Arg Term)) → (g : Name) → (gargs : List (Arg Term)) →  Nat → TC Term
generateMapRef f fargs g gargs 0 = return (def g (vArg (var f fargs) ∷ gargs))
generateMapRef f fargs g gargs (suc x) = bindTC (generateMapRef f fargs g gargs x)
                                                (λ y → return (lam visible (abs "lx" y)))

generateRefTerm : List Nat → TC (List (Arg Term))
generateRefTerm [] = return []
generateRefTerm (x ∷ xs) = bindTC (generateRefTerm xs)
                                  (λ xs' → return (vArg (var x []) ∷ xs'))

generateRefTerm' : (argInfo : List Bool) → List Nat → TC (List (Arg Term))
generateRefTerm' b [] = return []
generateRefTerm' (b ∷ bs) (x ∷ xs) = bindTC (generateRefTerm' bs xs)
                                            (λ xs' → bindTC (return b) λ
                                                            { true → return (hArg (var x []) ∷ xs') ;
                                                              false → return (vArg (var x []) ∷ xs') })
generateRefTerm' x y = return [] -- Invalid case

generateRefTermHid : List Nat → TC (List (Arg Term))
generateRefTermHid [] = return []
generateRefTermHid (x ∷ xs) = bindTC (generateRefTermHid xs)
                                     (λ xs' → return (hArg (var x []) ∷ xs'))

changeVisToHid : List (Arg Term) → TC (List (Arg Term))
changeVisToHid [] = return []
changeVisToHid (x ∷ xs) = bindTC (changeVisToHid xs)
                                 (λ xs' → bindTC (return x) λ
                                                  { (arg i term) → return (hArg term ∷ xs') })

generateRefTerm1 : List Nat → (List (Arg Term))
generateRefTerm1 [] = []
generateRefTerm1 (x ∷ xs) = (vArg (var x []) ∷ (generateRefTerm1 xs))

map' : ∀ {a b} {A : Set a} {B : Set b} → (A → TC B) → List A → TC (List B)
map' f []       = return []
map' f (x ∷ xs) = bindTC (map' f xs)
                         (λ xs' → bindTC (f x)
                         (λ x' → return (x' ∷ xs')))

{--
null : ∀ {a} {A : Set a} → List A → Bool
null []       = true
null (x ∷ xs) = false
--}

-- replicate : ∀ {a} {A : Set a} → (n : Nat) → A → List A
-- replicate zero    x = []
-- replicate (suc n) x = x ∷ replicate n x

addToList : Nat → List Nat → TC (List Nat)
addToList n [] = return []
addToList n (x ∷ xs) = bindTC (addToList n xs)
                              (λ xs' → return ((x + n) ∷ xs'))

isHidden : (i : ArgInfo) → TC Bool
isHidden (arg-info hidden r) = return true
isHidden (arg-info vis r) = return false

removeHidden : List (Arg Term) → TC (List (Arg Term))
removeHidden [] = return []
removeHidden ((arg i term) ∷ xs) = bindTC (isHidden i) λ
                                          { true → removeHidden xs ;
                                            false → bindTC (removeHidden xs)
                                                           (λ xs' → return ((arg i term) ∷ xs')) }

getArgsCount : Nat → Type → TC Nat
getArgsCount x (pi (arg info t1) (abs s t2)) = bindTC (getArgsCount (suc x) t2)
                                                      (λ c → return c)
getArgsCount x (agda-sort Level) = return x
getArgsCount x y = return x

getDiff : (lt : Nat) → (pars : Nat) → TC Nat
getDiff 0 0 = return 0
getDiff x 0 = return x
getDiff 0 x = return 0
getDiff (suc x) (suc y) = bindTC (getDiff x y)
                                 (λ n → return n)

getIndexValue : Nat → Nat → Type → TC Nat
getIndexValue ref par (pi (arg info t1) (abs s t2)) = bindTC (getIndexValue (suc ref) par t2)
                                                         (λ n → return n)
getIndexValue ref par (agda-sort Level) = bindTC (getDiff ref par)
                                            (λ i → return i)
getIndexValue ref par x = return ref

getIndex' : Name → TC Nat
getIndex' x = bindTC (getType x)
                    (λ t → bindTC (getParameters x)
                    (λ d → bindTC (getIndexValue zero d t)
                    (λ n → return n)))

getIndex : Name → List Nat → TC (List Nat)
getIndex x indLs =
  case null indLs of λ
   { true →
     do t ← getType x
        d ← getParameters x
        cns ← getConstructors x
        lcons ← getLength cns
        n ← getIndexValue zero d t
        return (Data.List.replicate lcons n)
   ; false → return indLs
   }

checkName : Name → List Name → TC Bool
checkName ctr [] = return false
checkName ctr (x ∷ xs) =
 if primQNameEquality ctr x
   then return true
   else checkName ctr xs

getCtrIndex : (ind : Nat) → Name → List Name → TC Nat
getCtrIndex ind ctr [] = return ind -- Invalid case
getCtrIndex ind ctr (x ∷ xs) =
  if primQNameEquality ctr x
    then return ind
    else getCtrIndex (suc ind) ctr xs

getListElement' : (n : Nat) → List Name → TC Name
getListElement' 0 (x ∷ xs) = return x
getListElement' (suc n) (x ∷ xs) = getListElement' n xs
getListElement' x y = return (quote ⊥) -- Invalid case

rmPars : (d : Nat) → (ty : Type) → TC Type
rmPars 0 ty = return ty
rmPars (suc x) (pi (arg i t1) (abs s t2)) = bindTC (rmPars x t2)
                                                   (λ t2' → return t2')
rmPars (suc x) ty = return unknown

rmHidPars : (ty : Type) → TC Type
rmHidPars (pi (arg (arg-info hidden rel) t1) (abs s t2)) = bindTC (rmHidPars t2)
                                                                  (λ t2' → return t2')
rmHidPars (pi (arg i t1) (abs s t2)) = bindTC (rmHidPars t2)
                                              (λ t2' → return (pi (arg i t1) (abs s t2')))
rmHidPars ty = return ty

getHidPars : (ty : Type) → TC Nat
getHidPars (pi (arg (arg-info hidden rel) t1) (abs s t2)) = bindTC (getHidPars t2)
                                                                   (λ n → return (suc n))
getHidPars (pi (arg i t1) (abs s t2)) = bindTC (getHidPars t2)
                                               (λ n → return n)
getHidPars ty = return 0

getHidArgs : Term → TC (List Bool) -- true for hidden args and false for visible args
getHidArgs (pi (arg i t1) (abs s t2)) = bindTC (getHidArgs t2)
                                               (λ t2' → bindTC (return i) λ
                                                           { (arg-info hidden rel) → return (true ∷ t2') ;
                                                             (arg-info vis rel) → return (false ∷ t2') })
getHidArgs x = return []

getHidArgs' : List ArgInfo → TC (List Bool) -- true for hidden args and false for visible args
getHidArgs' (x ∷ xs) = bindTC (getHidArgs' xs)
                              (λ xs' → bindTC (return x) λ
                                          { (arg-info hidden rel) → return (true ∷ xs') ;
                                            (arg-info vis rel) → return (false ∷ xs') })
getHidArgs' [] = return []

rmIndex : (indLength : Nat) → Type → TC Type
rmIndex 0 t = return t
rmIndex (suc x) (pi (arg info t1) (abs s t2)) = rmIndex x t2
rmIndex x y = return unknown -- Invalid case

changeCodomain' : Type → TC Type
changeCodomain' (def nm x) = return (def nm [])
changeCodomain' (pi (arg info dom) (abs s cdom)) = bindTC (changeCodomain' cdom)
                                                          (λ cdom' → return (pi (arg info dom) (abs s cdom')))
changeCodomain' x = return unknown

{-# TERMINATING #-}
checkIndexRef : (index : Nat) → Type → TC Bool
checkIndexRef index (pi (arg info t1) (abs s t2)) = bindTC (checkIndexRef index t1)
                                                          (λ b1 → bindTC (checkIndexRef (suc index) t2)
                                                          (λ b2 → return (_or_ b1 b2)))
checkIndexRef index (def x lsargs) = bindTC (map' (λ { (arg i term) → bindTC (checkIndexRef index term)
                                                                             (λ b → return b) }) lsargs)
                                           (λ lb → (checkTrue lb))
checkIndexRef index (var ref lsargs) = bindTC (return (eq ref index)) λ
                                        { true → return true ;
                                          false → bindTC (map' (λ { (arg i term) → bindTC (checkIndexRef index term)
                                                                             (λ b → return b) }) lsargs)
                                                                (λ lb → (checkTrue lb)) }
checkIndexRef index (con cn lsargs) = bindTC (map' (λ { (arg i term) → bindTC (checkIndexRef index term)
                                                                             (λ b → return b) }) lsargs)
                                           (λ lb → (checkTrue lb))
checkIndexRef index x = return false

checkIndexRef' : (cns : Type) → (inds : List Nat) → TC (List Bool)
checkIndexRef' cns [] = return []
checkIndexRef' cns (x ∷ xs) = bindTC (checkIndexRef' cns xs)
                                     (λ xs' → bindTC (changeCodomain' cns)
                                     (λ cns' → bindTC (checkIndexRef x cns')
                                     (λ x' → return (x' ∷ xs'))))

getIndexRef' : (index : List Nat) → (indLength : Nat) → Type → TC (List Bool)
getIndexRef' inds 0 x = checkIndexRef' x inds
getIndexRef' inds (suc x) (pi (arg info t1) (abs s t2)) = bindTC (return (map (λ z → z + 1) inds))
                                                                       (λ index' → bindTC (return (index' ∷L 0))
                                                                       (λ index'' → (getIndexRef' index'' x t2)))
getIndexRef' inds (suc x) (def ty args) = return [] -- cases where cons does not encode index in its type (Vec.[])
getIndexRef' inds x y = return []

getIndexRef : Name → Nat → Name → TC (List Bool)
getIndexRef R ind cn = bindTC (getParameters R)
                        (λ d → bindTC (getType cn)
                        (λ x → bindTC (rmPars d x)
                        (λ x' → (getIndexRef' [] ind x'))))

eqBool : Bool → Bool → Bool
eqBool true    true    = true
eqBool false false = true
{-# CATCHALL #-}
eqBool _       _       = false

isMemberBool : Bool → List Bool → TC Bool
isMemberBool b [] = return false
isMemberBool b (x ∷ xs) = bindTC (return (eqBool b x)) λ
                             { true → return true ;
                               false → (isMemberBool b xs) }

countBool : Bool → List Bool → TC Nat
countBool b [] = return 0
countBool b (x ∷ xs) = bindTC (countBool b xs)
                              (λ xs' → bindTC (return (eqBool b x)) λ
                                               { true → return (suc xs') ;
                                                 false → return xs' })

generateIndexRef-a : (inds : List Nat) → (trls : List Nat) → (ref1 : Nat) → (tref2 : Nat) → (iref : List Bool) → TC (List (Arg Term))
generateIndexRef-a inds trls ref1 ref2 (b ∷ bs) = bindTC (return b) λ
                                                          { false → bindTC (isMemberBool false bs) λ
                                                                           { false → bindTC (getListElement ref1 inds)
                                                                                           (λ i1 → return []) ; -- (hArg (var i1 []) ∷ [])) ; -- no recursive calls if remainder args are only true
                                                                             true → bindTC (generateIndexRef-a inds trls (suc ref1) ref2 bs)
                                                                                           (λ bs' → bindTC (getListElement ref1 inds)
                                                                                           (λ i1 → return bs')) } ; -- (hArg (var i1 []) ∷ bs'))) } ;
                                                            true → bindTC (generateIndexRef-a inds trls (suc ref1) (suc ref2) bs)
                                                                          (λ bs' → bindTC (getListElement ref2 trls)
                                                                                          (λ i2 → return (hArg (var i2 []) ∷ bs'))) }
generateIndexRef-a inds trls ref1 ref2 [] = return []

generateIndexRef-b : (trC : Nat) → (argRef : Nat) → (args : List (Arg Term)) → TC Type
generateIndexRef-b 0 argRef args = return (var argRef args)
generateIndexRef-b (suc x) argRef args = bindTC (generateIndexRef-b x argRef args)
                                               (λ ty → return (lam hidden (abs "_" ty)))

generateIndexRef-c : (inds : List Nat) → (iref : List Bool) → (argRef : Nat) → TC Type
generateIndexRef-c inds bs argRef = bindTC (countBool true bs)
                                        (λ trC → bindTC (generateRef trC)
                                        (λ trls → bindTC (return (map (λ z → z + trC) inds))
                                        (λ inds' → bindTC (generateIndexRef-a inds' trls 0 0 bs)
                                        (λ args' → (generateIndexRef-b trC argRef args')))))

generateIndexRef : (inds : List Nat) → (irefs : List (List Bool)) → (args : List Nat) → TC (List (Arg Term))
generateIndexRef inds (ib ∷ ibs) (x ∷ xs) = bindTC (generateIndexRef inds ibs xs)
                                                   (λ xs' → bindTC (isMemberBool false ib) λ
                                                                   { true → bindTC (generateIndexRef-c inds ib x)
                                                                                   (λ ty → return (vArg ty ∷ xs')) ;
                                                                     false → return (vArg (var x []) ∷ xs') } )
generateIndexRef inds [] [] = return []
generateIndexRef inds x y = return []

getRecArgs : (args : List Nat) → (inds : List Nat) → (irefs : List (List Bool)) → TC (List (Arg Term))
getRecArgs args inds irefs = bindTC (dropTC 1 args) -- drop C
                                    (λ args' → bindTC (takeTC 1 args) -- take C
                                    (λ argC → bindTC (generateRefTerm argC)
                                    (λ argC' → bindTC (generateIndexRef inds irefs args')
                                    (λ argsR → return (argC' ++L argsR)))))

generateMapRefRec : (f : Nat) → (fargs : List (Arg Term)) → (g : Name) → (args : List Nat) → (inds : List Nat) → (irefs : List (List Bool)) → Nat → TC Term
generateMapRefRec f fargs g args inds irefs 0 =  bindTC (getRecArgs args inds irefs)
                                                        (λ largs → return (def g (vArg (var f fargs) ∷ largs)))
generateMapRefRec f fargs g args inds irefs (suc x) = bindTC (generateMapRefRec f fargs g args inds irefs x)
                                                             (λ y → return (lam visible (abs "lx" y)))
getIndexRefInfo : (baseTyp : Name) → (indexList : List Nat) → (cons : List Name) → TC (List (List Bool))
getIndexRefInfo baseTyp [] [] = return []
getIndexRefInfo baseTyp (i ∷ is) (x ∷ xs) = bindTC (getIndexRefInfo baseTyp is xs)
                                                   (λ lbs' → bindTC (getIndexRef baseTyp i x)
                                                   (λ lb → return (lb ∷ lbs')))
getIndexRefInfo baseTyp x y = return [] -- Invalid case

checkCdm : Type → Type → TC Bool
checkCdm (def ty1 x) (def ty2 y) = return (primQNameEquality ty1 ty2)
checkCdm x (pi (arg info t1) (abs s t2)) = bindTC (checkCdm x t2) (λ y → return y)
checkCdm x y = return false

changeCodomain : (Cref : Nat) → Type → TC Type
changeCodomain Cref (def nm x) = return (var Cref [])
changeCodomain Cref (pi (arg info dom) (abs s cdom)) = bindTC (changeCodomain (suc Cref) cdom)
                                                              (λ cdom' → return (pi (arg info dom) (abs s cdom')))
changeCodomain Cref x = return unknown


foldl' : {A B : Set} → (B → A → TC B) → B → List A → TC B
foldl' f z [] = return z
foldl' f z (x ∷ xs) = bindTC (f z x)
                        (λ x' → bindTC (foldl' f x' xs)
                        (λ xs' → return xs'))
-- foldl f (f z x) xs

{-
{-# TERMINATING #-}
retExprRef' : (cons : Type) → TC Nat
retExprRef' (def x lsargs) = do ls ← map' (λ { (arg i term) →
                                             do t ← retExprRef' term
                                                return t }) lsargs
                                b ← isMember 1 ls
                                case b of λ
                                 { true → return 1
                                 ; false → return 0
                                 }
retExprRef' (con x lsargs) = do ls ← map' (λ { (arg i term) →
                                             do t ← retExprRef' term
                                                return t }) lsargs
                                b ← isMember 1 ls
                                case b of λ
                                 { true → return 1
                                 ; false → return 0
                                 }
retExprRef' (var ref lsargs) = return 1
retExprRef' x = return 0

retExprRef : (indType : Name) → (cons : Type) → TC Nat
retExprRef ind (pi (arg info t1) (abs s t2)) =
  do t2' ← retExprRef ind t2
     return t2'
retExprRef ind (def x lsargs) =
  case (primQNameEquality ind x) of λ
   { true →
     do cp ← getParameters ind
        lsargs' ← dropTC cp lsargs
        ln ← foldl' (λ {a (arg i term) →
                           do b' ← (retExprRef' term)
                              return (a + b') }) zero lsargs'
        return ln
   ; false → return 0
   }
retExprRef ind x = return 0


getExprRef : (indType : Name) → (cons : List Name) → TC (List Nat)
getExprRef ind [] = return []
getExprRef ind (c ∷ cs) =
  do cTy ← getType c
     l ← retExprRef ind cTy
     ls ← getExprRef ind cs
     return (l ∷ ls)

getExpRef : (indType : Name) → TC (List Nat)
getExpRef ind =
  do lcons ← (getConstructors ind)
     (getExprRef ind lcons)

-}


getBoolList : {A : Set} → List A → TC (List Bool)
getBoolList [] = return []
getBoolList (x ∷ xs) = do lb ← getBoolList xs
                          return (false ∷ lb)

setBl : (d : Nat) → List Bool → TC (List Bool)
setBl d [] = return []
setBl zero (x ∷ xs) = return (true ∷ xs)
setBl (suc x) (y ∷ ys) = do lb ← setBl x ys
                            return (y ∷ lb)

countB : List Bool → TC Nat
countB [] = return 0
countB (x ∷ xs) = do c ← countB xs
                     case x of λ
                      { true → return (suc c)
                      ; false → return c
                      }


{-# TERMINATING #-}
retExprRef' : (refLs : List Nat) → List Bool → (cons : Type) → TC (List Bool)
retExprRef' refLs lb (def x lsargs) = do ls ← foldl' (λ { lb' (arg i term) →
                                                               do lb'' ← retExprRef' refLs lb' term
                                                                  return lb'' }) lb lsargs
                                         return ls
retExprRef' refLs lb (con x lsargs) = do ls ← foldl' (λ { lb' (arg i term) →
                                                               do lb'' ← retExprRef' refLs lb' term
                                                                  return lb'' }) lb lsargs
                                         return ls
retExprRef' refLs lb (var ref lsargs) = do b ← isMember ref refLs
                                           case b of λ
                                            { true →
                                                 do lb' ← reverseTC lb
                                                    lb'' ← setBl ref lb'
                                                    lb''' ← reverseTC lb''
                                                    return lb'''
                                            ; false → return lb
                                            }
retExprRef' refLs lb x = return []

retExprRef : (indType : Name) → (refLs : List Nat) → (cons : Type) → TC Nat
retExprRef ind ref (pi (arg info t1) (abs s t2)) =
    do let ref' = (map (λ z → z + 1) ref)
           ref'' = (ref' ∷L 0)
       t2' ← retExprRef ind ref'' t2
       return t2'
retExprRef ind ref (def x lsargs) =
    case (primQNameEquality ind x) of λ
     { true →
       do cp ← getParameters ind
          lsargs' ← dropTC cp lsargs
          ref' ← dropTC cp ref
          lb ← getBoolList ref'
          lb' ← foldl' (λ {lb' (arg i term) →
                           do b' ← (retExprRef' ref' lb' term)
                              return b' }) lb lsargs'
          ln ← countB lb'
          return ln
     ; false → return 0
     }
retExprRef ind ref x = return 0


getExprRef : (indType : Name) → (cons : List Name) → TC (List Nat)
getExprRef ind [] = return []
getExprRef ind (c ∷ cs) =
    do cTy ← getType c
       l ← retExprRef ind [] cTy
       ls ← getExprRef ind cs
       return (l ∷ ls)

getExpRef : (indType : Name) → TC (List Nat)
getExpRef ind =
    do lcons ← (getConstructors ind)
       (getExprRef ind lcons)


{-# TERMINATING #-}
printArgs : List (Arg Term) → TC ⊤
printArgs [] = return tt
printArgs (x ∷ xs) = bindTC (return x) λ
                            { (arg info (var x args)) → bindTC (debugPrint "tc.sample.debug" 12 (strErr (showNat x) ∷ []))
                                                         (λ _ → printArgs xs) ;
                              (arg info (def y args')) → bindTC (debugPrint "tc.sample.debug" 12 (strErr "term is ---> " ∷ []))
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (termErr (def y []) ∷ []))
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (strErr "sub start ---> " ∷ []))
                                                         (λ _ → bindTC (printArgs args')
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (strErr "sub end ---> " ∷ []))
                                                         (λ _ → printArgs xs))))) ;
                              (arg info (con y args')) → bindTC (debugPrint "tc.sample.debug" 12 (strErr "constructor is ---> " ∷ []))
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (termErr (con y []) ∷ []))
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (strErr "sub start ---> " ∷ []))
                                                         (λ _ → bindTC (printArgs args')
                                                         (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (strErr "sub end ---> " ∷ []))
                                                         (λ _ → printArgs xs))))) ;
                              (arg info term) → bindTC (debugPrint "tc.sample.debug" 12 (termErr term ∷ []))
                                                         (λ _ → printArgs xs) }

printList : List Nat → TC ⊤
printList [] = return tt
printList (x ∷ xs) = bindTC (debugPrint "tc.sample.debug" 20 (strErr "printList **" ∷ strErr (showNat x) ∷ []))
                            (λ _ → printList xs)

{-# TERMINATING #-}
updateArgs : (refList : List Nat) → List (Arg Term) → TC (List (Arg Term))
updateArgs refList [] = return []
updateArgs refList (x ∷ xs) =
  do xs' ← updateArgs refList xs
     case x of λ
       { (arg info (var dis args)) →
         do args' ← updateArgs refList args
            refList' ← reverseTC refList
            x' ← getListElement dis refList'
            -- debugPrint "tc.sample.debug" 12 (strErr "Inside updateAgrs" ∷ [])
            -- printList refList'
            -- debugPrint "tc.sample.debug" 12 (strErr (showNat dis) ∷ strErr " and " ∷ strErr (showNat x') ∷ [])
            return ((arg info (var x' args')) ∷ xs')
       ; (arg info (def y args)) →
         do args' ← updateArgs refList args
            return ((arg info (def y args')) ∷ xs')
       ; (arg info (con y args)) →
         do args' ← updateArgs refList args
            return ((arg info (con y args')) ∷ xs')
       ; (arg info term) →
         do -- debugPrint "tc.sample.debug" 12 (strErr "unmatched case" ∷ [])
            return ((arg info term) ∷ xs')
       }


changeCodomainInd : (Cref : Nat) → (refL : List Nat) → (pars : Nat) → Type → TC Type
changeCodomainInd Cref refL pars (def nm x) =
  do pars' ← generateRef pars
     pars'' ← generateRefTerm pars'
     d ← getParameters nm
     index ← dropTC d x
     -- debugPrint "tc.sample.debug" 12 (strErr "changeCodomainInd 1 -----> " ∷ [])
     -- printArgs x
     index' ← updateArgs refL index
     indexH ← changeVisToHid index
     -- debugPrint "tc.sample.debug" 12 (strErr "changeCodomainInd -----> " ∷ [])
     -- printList refL
     -- debugPrint "tc.sample.debug" 12 (strErr "ListEnd ----" ∷ [])
     -- debugPrint "tc.sample.debug" 12 (termErr (def nm []) ∷ [])
     -- printArgs indexH
     return (var Cref (indexH ++L (vArg (var pars pars'') ∷ [])))
changeCodomainInd Cref refL pars (pi (arg info dom) (abs s cdom)) =
  do let refL' = map (λ z → z + 1) refL
     cdom' ← changeCodomainInd (suc Cref) refL' (suc pars) cdom
     return (pi (arg info dom) (abs s cdom'))
changeCodomainInd Cref refL pars x =
  return unknown

getTypeLn : Nat → Type → TC Nat
getTypeLn ref (pi (arg info t1) (abs s t2)) = bindTC (getTypeLn (suc ref) t2)
                                                     (λ ref' → return ref')
getTypeLn ref (agda-sort Level) = return ref
getTypeLn ref x = return 0

getBaseType : Type → TC Type
getBaseType (pi (arg info t1) (abs s t2)) = getBaseType t2

getBaseType (def x args) = return (def x args)
getBaseType x = return unknown

getConsTypes : List Name → TC (List Type)
getConsTypes [] = return []
getConsTypes (x ∷ xs) =
  do t ← getType x
     xt ← getConsTypes xs
     return (t ∷ xt)

{--
_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map _ []       = []
map f (x ∷ xs) = f x ∷ map f xs

length : ∀ {a} {A : Set a} → List A → Nat
length []       = 0
length (x ∷ xs) = 1 + length xs
--}
