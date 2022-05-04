{-# OPTIONS --cumulativity #-}

open import Library

module clase06.ConstruccionesSet where
 
 open import Categories.Sets
 open import clase06.Construcciones Sets 

 {- Ejercicios
   -- Probar que Sets tiene objeto terminal, productos, inicial, y coproductos
  -}
 
 ×func : {A B C : Set} → (C → A) → (C → B) → C → A × B 
 ×func f g c = (f c) , (g c)

 SetsHasProducts : Products
 SetsHasProducts = prod _×_ fst snd ×func refl refl (λ p q → ext (λ c → sym (cong₂ _,_ (cong-app (sym p) c) (cong-app (sym q) c))))

 OneSet : Terminal ⊤
 OneSet = term (λ _ → tt) refl

 -------------------------------------------------
 data _⊎_{a b : Level}(A : Set a)(B : Set b) : Set (a ⊔ b) where
     Inl : A → A ⊎ B
     Inr : B → A ⊎ B

 ⊎func : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
 ⊎func f g (Inl x) = f x
 ⊎func f g (Inr x) = g x

 unicidad-coprod : {A B C : Set} {h : A ⊎ B → C} {f : A → C} {g : B → C} → 
                   (λ x → h (Inl x)) ≅ f → (λ x → h (Inr x)) ≅ g → (x : A ⊎ B) →  h x ≅ ⊎func f g x
 unicidad-coprod p q (Inl x) = cong-app p x
 unicidad-coprod p q (Inr x) = cong-app q x

 SetsHasCoproducts : Coproducts
 SetsHasCoproducts = coproduct _⊎_ Inl Inr ⊎func refl refl (λ p q → ext (unicidad-coprod p q))

--------------------------------------------------
 fzero : {X : Set} → ⊥ → X
 fzero ()

 fzero≅f : {X : Set} {f : ⊥ → X} → (x : ⊥) → fzero x ≅ f x
 fzero≅f ()

 ZeroSet : Initial ⊥
 ZeroSet = init fzero (λ {X} {f} → (ext (λ x → fzero≅f {X} {f} x)))
--------------------------------------------------
 