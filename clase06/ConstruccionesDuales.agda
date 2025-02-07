
module clase06.ConstruccionesDuales where

open import Library
open import Categories

private 
  variable
   a b : Level
   C : Cat {a} {b}

open import clase06.Construcciones
open import Categories.Iso

open Cat
open Initial
open Iso
open Terminal
-------------------------------------------------
 {- Probar que un objeto terminal es inicial en la categoría dual y viceversa -}
TerminalInitialDuality : {X : Obj C} → Terminal C X → Initial (C Op) X
TerminalInitialDuality ter = init (t ter) (law ter)


InitialTerminalDuality : {X : Obj C} → Initial C X → Terminal (C Op) X
InitialTerminalDuality ini  = term (i ini) (law ini)

--------------------------------------------------
 
c-cop : {A B : Obj C} → (fun : Hom C A B) → Iso C fun → Iso (C Op) fun 
c-cop fun (iso inv law1 law2) = iso inv law2 law1

cop-c : {A B : Obj C} → (fun : Hom C A B) → Iso (C Op) fun → Iso C fun 
cop-c fun (iso inv law1 law2) = iso inv law2 law1

 {- Probar que dos objetos iniciales son necesariamente isomorfos *usando dualidad* -}
InitialIso : (I I' : Obj C)
            → (p : Initial C I)
            → (q : Initial C I')
            → Iso C (i p {I'})
InitialIso {C = C} I I' p q = cop-c {A = I} {B = I'} (i p {I'}) (TerminalIso (C Op) I I' (InitialTerminalDuality p) (InitialTerminalDuality q))
 

--------------------------------------------------------
-- Probar que los coproductos son productos en la categoría dual
ProductCoproductDuality : Products C
                        → Coproducts (C Op)
ProductCoproductDuality (prod _×_₁ π₁ π₂ ⟨_,_⟩ law1 law2 law3) = coproduct _×_₁ π₁ π₂ ⟨_,_⟩ law1 law2 law3

CoproductProductDuality : Coproducts C
                        → Products (C Op)
CoproductProductDuality (coproduct _+_ inl inr [_,_] law1 law2 law3) = prod _+_ inl inr [_,_] law1 law2 law3


--------------------------------------------------
open Coproducts

 {- Probar que los coproductos son únicos hasta un isomorfismo usando dualidad -}
CoproductIso : ∀{A B}(X Y : Coproducts C) → Iso C ([_,_] X {A} {B} (inl Y) (inr Y))
CoproductIso {C = C} {A = A} {B = B} X Y = cop-c (([_,_] X {A = A} {B = B} (inl Y) (inr Y))) 
                                                 (ProductIso (C Op) (CoproductProductDuality X) (CoproductProductDuality Y))


--------------------------------------------------
