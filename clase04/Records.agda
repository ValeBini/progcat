
module Records where

open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional as Ext

-- postulamos extensionalidad
postulate ext : ∀{a b} → Ext.Extensionality a b

{- Veremos, el uso de records para definir estructuras algebraicas -}


-- MONOIDES

{- Notar el uso de de Set₁ en lugar de Set ya que tenemos que
 situarnos en el nivel siguiente a Set₀ = Set, para hablar de cosas en
 Set (como carrier).

Los subindices son ₀ = \_0 y ₁ = \_1
 -}

record Monoid : Set₁  where
  infixr 7 _∙_
  -- constructor monoid
  field  Carrier : Set
         _∙_     : Carrier → Carrier → Carrier  {- ∙ = \. -}
         ε       : Carrier   {- ε = \epsilon -}
         lid     : {x : Carrier} → ε ∙ x ≡ x
         rid     : {x : Carrier} → x ∙ ε ≡ x
         assoc   : {x y z : Carrier} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z) 

{- ¿Qué sucede si queremos usar un Carrier en Set₁? ¿o en Set₂? -}

{- Al escribir las ecuaciones estamos tomando una decisión sobre la noción de igualdad 
 En esta definición elegimos la igualdad proposicional
-}

open import Data.Nat
open import Data.Nat.Properties using (+-identityʳ ; *-zeroʳ ; +-assoc ; *-distribˡ-+ ; *-comm)

-- Monoide de Naturales y suma

module NatMonoid where


  NatMonoid : Monoid
  NatMonoid = record
    { Carrier = ℕ 
    ; _∙_ = _+_ 
    ; ε = 0 
    ; lid = refl 
    ; rid = λ {x} → +-identityʳ x ; 
    assoc = λ {x} {y} {z} → +-assoc x y z }

open NatMonoid


--------------------------------------------------
{- Ejercicio: Probar que las listas son un monoide -}

open ≡-Reasoning
open import Data.List hiding (foldr)
open import Data.List.Properties

module ListMonoid where
  ListMonoid : Set → Monoid
  ListMonoid X = record
       {Carrier = List X 
       ; _∙_ = _++_ 
       ; ε = [] 
       ; lid = λ {l} → ++-identityˡ l 
       ; rid = λ {l} →  ++-identityʳ l 
       ; assoc = λ {l1} {l2} {l3} → ++-assoc l1 l2 l3 }

open ListMonoid
--------------------------------------------------

{- Ejercicio: Probar que para todo monoide M, N, el producto
   cartesiano de los respectivos soportes (Carrier M × Carrier N)
   es  el soporte de un monoide

 Ayuda : puede ser útil cong₂

-}

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)

module ProductMonoid where
  ProductMonoid : (M N : Monoid) → Monoid
  ProductMonoid M N = record
                        { Carrier = CarrierM × CarrierN 
                        ; _∙_ = λ (xm , xn) (ym , yn) → xm ∙M ym , xn ∙N yn
                        ; ε = εM , εN 
                        ; lid = λ {(m , n)} → cong₂ _,′_ lidM lidN
                        ; rid = λ {(m , n)} → cong₂ _,′_ ridM ridN
                        ; assoc = λ {(m1 , n1)} {(m2 , n2)} {(m3 , n3)} → cong₂ _,′_ assocM assocN }
                    where open Monoid M renaming (ε to εM ; Carrier to CarrierM ; _∙_ to _∙M_ ; lid to lidM ; rid to ridM ; assoc to assocM)
                          open Monoid N renaming (ε to εN ; Carrier to CarrierN ; _∙_ to _∙N_ ; lid to lidN ; rid to ridN ; assoc to assocN)

--------------------------------------------------
open import Function

-- Monoide de endofunciones
EndoMonoid : Set → Monoid
EndoMonoid X = record
                 { Carrier = X → X
                 ; _∙_ = _∘′_
                 ; ε = id
                 ; lid = refl
                 ; rid = refl
                 ; assoc = refl }


module Cayley where

  open Monoid using (Carrier)

  Cayley : Monoid → Monoid
  Cayley M = EndoMonoid (Carrier M) 

  rep : (M : Monoid) → Carrier M → Carrier (Cayley M)
  rep M x = λ y → x ∙ y
           where open Monoid M

  abs : (M : Monoid) → Carrier (Cayley M) → Carrier M
  abs M f = f ε
           where open Monoid M

  lemma : (M : Monoid) → {x : Carrier M} →
          abs M (rep M x) ≡ x
  lemma M = rid
           where open Monoid M

module Monoid-Homomorphism where
 open Monoid

-- Homomorfismos de monoides
 record Is-Monoid-Homo (M N : Monoid)(morph : Carrier M → Carrier N) : Set₁ where
   open Monoid M renaming (ε to ε₁ ;  _∙_ to _∙₁_)
   open Monoid N renaming (ε to ε₂ ;  _∙_ to _∙₂_)
   field
    preserves-unit : morph ε₁ ≡ ε₂
    preserves-mult : ∀{x y} → morph (x ∙₁ y) ≡ morph x ∙₂ morph y 

open Monoid-Homomorphism
open Cayley

rep-is-monoid-homo : {M : Monoid} → Is-Monoid-Homo M (Cayley M) (rep M)
rep-is-monoid-homo {M} = record {
                         preserves-unit = ext (λ x → lid)
                       ; preserves-mult = ext (λ x → assoc) }
                  where open Monoid M

--------------------------------------------------
{- Ejercicio: Probar que length es un homorfismo de monoides -}

{-
length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs
-} 

lenx++y : {A : Set} → (l1 l2 : List A) → length (l1 ++ l2) ≡ length l1 + length l2
lenx++y [] l2 = refl
lenx++y (x ∷ l1) l2 = begin 
                        length ((x ∷ l1) ++ l2)
                      ≡⟨ refl ⟩
                        length (x ∷ (l1 ++ l2)) 
                      ≡⟨ refl ⟩
                        1 + length (l1 ++ l2)
                      ≡⟨ cong₂ _+_ refl (lenx++y l1 l2) ⟩
                        1 + length l1 + length l2
                      ≡⟨ refl ⟩
                        length (x ∷ l1) + length l2
                      ∎

length-is-monoid-homo : {A : Set} → Is-Monoid-Homo (ListMonoid A) NatMonoid length
length-is-monoid-homo {A} = record 
                          { preserves-unit = refl 
                          ; preserves-mult =  λ {ls1} {ls2} → lenx++y ls1 ls2 }
                        where open Monoid (ListMonoid A) renaming (ε to εL ; _∙_ to _∙L_)
                              open Monoid NatMonoid renaming (ε to εN ; _∙_ to _∙N_)

--------------------------------------------------
{- Ejercicio: Probar que multiplicar por una constante es un es un homorfismo de NatMonoid -}

const*-is-monoid-homo : (c : ℕ) → Is-Monoid-Homo NatMonoid NatMonoid (_*_ c)
const*-is-monoid-homo c = record 
                        { preserves-unit = *-zeroʳ c 
                        ; preserves-mult = λ {x} {y} → *-distribˡ-+ c x y }
                      where open Monoid NatMonoid


--------------------------------------------------
module Foldr (M : Monoid) where

 open Monoid M

 {- Ejercicio : Definir foldr y probar que (foldr _∙_ ε) es un homorfismo de monoides -}


 foldr : {A B : Set} → (A → B → B) → B → List A → B
 foldr _⊗_ e [] = e
 foldr _⊗_ e (x ∷ xs) = x ⊗ (foldr _⊗_ e xs)

 foldr++ : {M : Monoid} → (l1 l2 : List (Monoid.Carrier M)) → 
          foldr (Monoid._∙_ M) (Monoid.ε M) (l1 ++ l2) ≡ 
          (Monoid._∙_ M) (foldr (Monoid._∙_ M) (Monoid.ε M) l1) (foldr (Monoid._∙_ M) (Monoid.ε M) l2)
 foldr++ {M} [] ys = (sym (lidM {foldr {MC} {MC} _∙M_ εM ys}))
                   where open Monoid M renaming (Carrier to MC ; _∙_ to _∙M_ ; ε to εM ; lid to lidM)
 foldr++ {M} (x ∷ xs) ys = begin 
                              foldr _∙M_ εM ((x ∷ xs) ++ ys)
                           ≡⟨ refl ⟩
                              foldr _∙M_ εM (x ∷ (xs ++ ys))
                           ≡⟨ refl ⟩
                              (x ∙M (foldr _∙M_ εM (xs ++ ys)))
                           ≡⟨ cong (_∙M_ x) (foldr++ xs ys) ⟩
                              (x ∙M ((foldr _∙M_ εM xs) ∙M (foldr _∙M_ εM ys)))
                           ≡⟨ sym (assocM {x} {(foldr _∙M_ εM xs)} {(foldr _∙M_ εM ys)}) ⟩
                              ((x ∙M (foldr _∙M_ εM xs)) ∙M (foldr _∙M_ εM ys))
                           ≡⟨ refl ⟩
                              (foldr _∙M_ εM (x ∷ xs) ∙M foldr _∙M_ εM ys)
                           ∎
                         where open Monoid M renaming (Carrier to MC ; _∙_ to _∙M_ ; ε to εM ; lid to lidM ; assoc to assocM)

 foldr-is-monoid-homo : {M : Monoid} → Is-Monoid-Homo (ListMonoid (Monoid.Carrier M)) M (foldr (Monoid._∙_ M) (Monoid.ε M))
 foldr-is-monoid-homo {M} = record 
                          { preserves-unit = refl 
                          ; preserves-mult = λ {xs} {ys} → foldr++ xs ys }
                          where open Monoid M renaming (_∙_ to _∙ₘ_ ; ε to εₘ ; Carrier to CarrierM)
                                open Monoid (ListMonoid (Monoid.Carrier M)) renaming (_∙_ to _∙ₗ_ ; ε to εₗ ; Carrier to CarrierL)


--------------------------------------------------

{- Isomorfismos entre conjuntos -}

record Iso (A : Set)(B : Set) : Set where
  field fun : A → B
        inv : B → A
        law1 : ∀ b → fun (inv b) ≡ b
        law2 : ∀ a → inv (fun a) ≡ a

open Iso

-----------------------------

{- Ejercicio : introducir un tipo de datos (record) ⊤ con un único habitante y
probar que  ℕ es isomorfo a List ⊤ -}

record ⊤ : Set where
  instance constructor tt

nat→list : ℕ → (List ⊤)
nat→list zero = []
nat→list (suc n) = tt ∷ (nat→list n)

list→nat : (List ⊤) → ℕ
list→nat [] = 0
list→nat (x ∷ xs) = suc (list→nat xs)

id-list⊤ : (l : List ⊤) → nat→list (list→nat l) ≡ l
id-list⊤ [] = refl
id-list⊤ (x ∷ xs) = begin 
                      nat→list (list→nat (x ∷ xs))
                    ≡⟨ refl ⟩
                      nat→list (suc (list→nat xs))
                    ≡⟨ refl ⟩
                      tt ∷ (nat→list (list→nat xs))
                    ≡⟨ cong (_∷_ tt) (id-list⊤ xs) ⟩
                      tt ∷ xs
                    ≡⟨ refl ⟩
                      x ∷ xs
                    ∎

id-nat⊤ : (n : ℕ) → list→nat (nat→list n) ≡ n 
id-nat⊤ zero = refl
id-nat⊤ (suc n) rewrite id-nat⊤ n = refl

iso-nat-list⊤ : Iso ℕ (List ⊤)
iso-nat-list⊤ = record 
              { fun = nat→list 
              ; inv = list→nat 
              ; law1 = id-list⊤
              ; law2 = id-nat⊤ }


{- Ejercicio: introducir un constructor de tipos Maybe (o usar Data.Maybe) y probar que
Maybe ℕ es isomorfo a ℕ -}

open import Data.Maybe

maybe→nat : (Maybe ℕ) → ℕ
maybe→nat nothing = 0
maybe→nat (just x) = suc x

nat→maybe : ℕ → (Maybe ℕ)
nat→maybe zero = nothing
nat→maybe (suc n) = just n

id-maybe : (m : Maybe ℕ) → nat→maybe (maybe→nat m) ≡ m 
id-maybe nothing = refl
id-maybe (just x) = refl

id-natm : (n : ℕ) → maybe→nat (nat→maybe n) ≡ n 
id-natm zero = refl
id-natm (suc n) = refl

iso-maybe-nat : Iso (Maybe ℕ) ℕ
iso-maybe-nat = record 
              { fun = maybe→nat 
              ; inv = nat→maybe 
              ; law1 = id-natm 
              ; law2 = id-maybe }

{- Ejercicio: introducir un constructor de tipos _×_ para productos
cartesianos (o usar el de Data.Product) y probar que (A → B × C) es
isomorfo a (A → B) × (A → C) para todos A, B, y C, habitantes de Set -}

product→ : {A B C : Set} → (A → B × C) → (A → B) × (A → C)
product→ fp = (λ a → fst (fp a)) , λ a → snd (fp a)

product← : {A B C : Set} → (A → B) × (A → C) → (A → B × C)
product← (fb , fc) = λ a →  (fb a) , (fc a)


iso-product : {A B C : Set} → Iso (A → B × C) ((A → B) × (A → C))
iso-product {A} {B} {C} = record 
                        { fun = product→ 
                        ; inv = product←
                        ; law1 = λ b → refl 
                        ; law2 = λ a → refl }


{- Ejercicio: construir isomorfismos entre Vec A n × Vec B n y
Vec (A × B) n para todos A, B habitantes de Set y n natural -}

open import Data.Vec

vec→ : {A B : Set} → {n : ℕ} → Vec A n × Vec B n → Vec (A × B) n 
vec→ ([] , []) = []
vec→ (a ∷ veca , b ∷ vecb) = (a , b) ∷ (vec→ (veca , vecb))

vec← : {A B : Set} → {n : ℕ} → Vec (A × B) n → Vec A n × Vec B n
vec← [] = [] , []
vec← ((a , b) ∷ v) = (a ∷ fst (vec← v)) , (b ∷ snd (vec← v))

id-1 : {A B : Set} → {n : ℕ} → (v : Vec (A × B) n) → vec→ (vec← v) ≡ v
id-1 [] = refl
id-1 (x ∷ v) rewrite id-1 v = refl

id-2 : {A B : Set} → {n : ℕ} → (v : Vec A n × Vec B n) → vec← (vec→ v) ≡ v 
id-2 ([] , []) = refl
id-2 (a ∷ va , b ∷ vb) = begin 
                            vec← (vec→ (a ∷ va , b ∷ vb))
                         ≡⟨ refl ⟩
                            vec← ((a , b) ∷ (vec→ (va , vb)))
                         ≡⟨ refl ⟩
                            (a ∷ fst (vec← (vec→ (va , vb)))) , (b ∷ snd (vec← (vec→ (va , vb))))
                         ≡⟨ cong (λ x → a ∷ fst x , b ∷ snd x) (id-2 (va , vb)) ⟩
                            (a ∷ fst (va , vb)) , (b ∷ snd (va , vb))
                         ≡⟨ refl ⟩
                            a ∷ va , b ∷ vb
                         ∎

iso-vec : {A B : Set} → {n : ℕ} → Iso (Vec A n × Vec B n) (Vec (A × B) n)
iso-vec = record 
        { fun = vec→
        ; inv = vec← 
        ; law1 = id-1 
        ; law2 = id-2 }


--------------------------------------------------
{- Ejercicio Extra
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app
-}

Biyectiva : {X Y : Set}(f : X → Y) → Set
Biyectiva {X} {Y} f = (y : Y) → Σ X (λ x → (f x ≡ y) × (∀ x' → f x' ≡ y → x ≡ x')) 

