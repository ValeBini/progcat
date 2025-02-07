module Categories where

{- importamos extensionalidad, proof irrelevance -}
open import Library

open import Relation.Binary.PropositionalEquality  


--------------------------------------------------
{- Definición de Categoría -}
{-
 - Una colección de objetos  (denotado con Obj (C))
 - Conjuntos de flechas entre objetos (Sean A, B ∈ Obj(C) , hom (A, B))
 - todo objeto tiene una flecha identidad (id : A → A)
 - todo par de flechas "compatibles" puede componerse ( ∘ )
 - la composición es asociativa, con la flecha identidad como unidad. 
     (f ∘ g) ∘ h = f ∘ (g ∘ h)
     f ∘ id = id ∘ f = f 
-}


record Cat : Set₂ where
  infix 7 _∙_ 
  field Obj : Set₁
        Hom : Obj → Obj → Set
        iden : ∀ {X} → Hom X X
        _∙_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl : ∀ {X Y} {f : Hom X Y} → iden ∙ f ≡ f  
        idr : ∀ {X Y} {f : Hom X Y} → f ∙ iden ≡ f
        ass : ∀ {X Y Z W} {f : Hom Y Z} {g : Hom X Y}{h : Hom W X} →
              (f ∙ g) ∙ h ≡ f ∙ (g ∙ h)
        

--------------------------------------------------
{- El típico ejemplo de categoría es la categoría Set de conjuntos y
   funciones entre los mismos.
-}


Sets : Cat
Sets = record
         { Obj = Set
         ; Hom = λ X Y → X → Y  
         ; iden = id
         ; _∙_ = λ f g → f ∘ g  
         ; idl = refl
         ; idr = refl
         ; ass = refl
         } 


--------------------------------------------------
{- Para cada categoría existe la categoría dual, que consiste de los
mismos objetos, pero con las flechas invertidas.
   Cₒₚ :  
   Objetos : Obj (C) 
   Hom (X, Y) : Hom (Y, X) ∈ C   

-}

_Op : Cat → Cat
C Op =  let open Cat C in
        record
         { Obj = Obj
         ; Hom = λ X Y → Hom Y X 
         ; iden = iden
         ; _∙_ = λ f g → g ∙ f 
         ; idl = idr
         ; idr = idl
         ; ass = sym ass
         }  



--------------------------------------------------
{- Categoría Discreta

   Una categoría discreta es una categoría en la que los únicos
morfismos son identidades. La composición y ecuaciones de coherencia
son triviales.
-}


Discrete : Set₁ → Cat
Discrete X = record
               { Obj = X
               ; Hom = λ _ _ → ⊤ 
               ; iden = tt  
               ; _∙_ = λ _ _ → tt
               ; idl = refl
               ; idr = refl
               ; ass = refl
               } 



{- A menudo nos queremos "olvidar" de los morfismos de una
categoría. Es decir, miramos a la categoría como una categoría
discreta. Esto se nota en lenguaje categórico como |C| -}

∣_∣ : Cat → Cat
∣ C ∣ = Discrete (Cat.Obj C)

--------------------------------------------------
{- Categoría Producto -}
{- Dadas dos categorías, podemos formar la categoría producto 
   Los objetos son el producto cartesiano de los objetos
   Los morfismos son pares de flechas.


  Obj (C × D) = Obj (C) × Obj(D)
  
         (X , Y) ∈ Obj (C × D) donde X ∈ Obj (C) ∧ y ∈ Obj (D) 

  Hom ((X, Y), (X', Y')) = Hom (X, X') × Hom (Y , Y')

         f : X → X' ∈ Hom (X, X') ∧ g : Y → Y' ∈ Hom (Y, Y') ⇒ (f, g) ∈ Hom ((X, Y), (X', Y'))   

  (f , g) ∘ (f' , g') = (f ∘ f' ,  g ∘ g')
 
  id = (id , id)

-}

_×C_ : Cat → Cat → Cat
C ×C D = record
           { Obj = Obj₁ × Obj₂
           ; Hom = λ {(X , Y) (X' , Y') → Hom₁ X X' × Hom₂ Y Y' }
           ; iden = (iden₁ , iden₂)
           ; _∙_ = λ {(f , g) (f' , g') → f ∙₁ f' , (g ∙₂ g')} 
           ; idl = cong₂ _,_ idl₁ idl₂
           ; idr = cong₂ _,_ idr₁ idr₂
           ; ass = cong₂ _,_ ass₁ ass₂
           } 
           where open Cat C renaming (Obj to Obj₁ ; Hom to Hom₁ ; iden to iden₁ ; _∙_ to _∙₁_ ; idl to idl₁ ; idr to idr₁ ; ass to ass₁)
                 open Cat D renaming (Obj to Obj₂ ; Hom to Hom₂ ; iden to iden₂ ; _∙_ to _∙₂_ ; idl to idl₂ ; idr to idr₂ ; ass to ass₂)  
          


--------------------------------------------------
{- Familia de Conjuntos -}
{- Los objetos son familias de conjuntos
   (conjuntos indexados por un conjunto de índices)

  Los morfismos son funciones que preservan el índice.
 
  Objetos:  {Aᵢ} i ∈ I
  Flechas : Aᵢ → Bᵢ    
-}


Fam : Set → Cat
Fam I = record
          { Obj = I → Set
          ; Hom = λ A B → ∀ {i} → A i → B i  
          ; iden = id
          ; _∙_ = λ f g → f ∘ g  
          ; idl = refl
          ; idr = refl
          ; ass = refl
          } 


--------------------------------------------------
{- Ejemplo extendido: Categorías Slice -}

{- Dada una categoría C, los objetos de un slice
   sobre un objeto I, son morfismos con codominio I
-}


module Slice (C : Cat) where 

  open Cat C

  record Slice₀ (I : Obj) : Set₁ where
    constructor _,_
    field
     base : Obj
     homBase : Hom base I
     
  open Slice₀

  {- record para representar los morfismos de la categoría -}
  record Slice₁ (I : Obj) (X Y : Slice₀ I) : Set where 
    constructor _,_
    field
       baseHom : Hom (base X) (base Y)  -- h  
       prop : (homBase Y) ∙ baseHom ≡ homBase X   -- g ∙ h = f

  {- la composición es simplemente pegar triángulos -}
  Slice-comp :  {I : Obj} {X Y Z : Slice₀ I} →
                Slice₁ I Y Z → Slice₁ I X Y → Slice₁ I X Z
  Slice-comp {I} {X , f} {Y , g} {Z , i} (h , p) (h' , q) =
    ( h ∙ h') , (proof  i ∙ (h ∙ h')
                         ≡⟨ sym ass ⟩
                         (i ∙ h) ∙ h'
                         ≡⟨ cong (λ j → j ∙ h') p ⟩
                         g ∙ h'
                         ≡⟨ q ⟩
                         f
                         ∎ )
  
  open Slice₁

  {- veamos como funciona proof irrelevance -}
  Slice₁-eq : {I : Obj} {X Y : Slice₀ I} {h h' : Slice₁ I X Y} →
              (baseHom h) ≡ (baseHom h')  →
              h ≡ h'
  Slice₁-eq {I} {X , f} {Y , g} {h , p} {.h , q} refl = cong (λ p → (h , p)) (ir p q)
 

  Slice : (I : Obj) → Cat
  Slice I = record
              { Obj = Slice₀ I
              ; Hom = Slice₁ I 
              ; iden = iden , idr
              ; _∙_ = Slice-comp  
              ; idl = Slice₁-eq idl
              ; idr = Slice₁-eq idr
              ; ass = Slice₁-eq ass
              }
 
 
--------------------------------------------------

{- Ejercicio: Definir la categoría con un sólo objeto ⊤, y que sus
morfismos son los elementos de un monoide M -}

module CatMon where

 open import Records-completo hiding (Iso ; ⊤)

 CatMon : Monoid → Cat
 CatMon M = let open Monoid M 
   in record
   { Obj = Lift _ ⊤
   ; Hom = λ _ _ → Carrier
   ; iden = ε
   ; _∙_ = _∙_
   ; idl = lid
   ; idr = rid
   ; ass = assoc
   } 


--------------------------------------------------
{- Ejercicio: Definir la categoría en que los objetos son monoides,
  y las flechas son homomorfismos de monoides
-}

module MonCat where

 open import Records-completo hiding (Iso)
 open Monoid
 open Is-Monoid-Homo

 record Monoid-Morph (M N : Monoid) : Set where
   constructor monoid-morph
   field 
      morph : Carrier M → Carrier N
      is-monoid-morph : Is-Monoid-Homo M N morph

 open Monoid-Morph

 Monoid-comp : {X Y Z : Monoid} → Monoid-Morph Y Z → Monoid-Morph X Y → Monoid-Morph X Z
 Monoid-comp {X} {Y} {Z} myz mxy = monoid-morph 
                                       ((morph myz) ∘ (morph mxy)) 
                                       (is-monoid-homo 
                                          (proof
                                                morph myz (morph mxy (εX))
                                             ≡⟨ cong (morph myz) (preserves-unit (is-monoid-morph mxy)) ⟩
                                                morph myz (εY)
                                             ≡⟨ preserves-unit (is-monoid-morph myz) ⟩
                                                εZ
                                             ∎)
                                          (λ {x} {y} → 
                                             proof
                                                morph myz (morph mxy ((x ∙X y))) 
                                             ≡⟨ cong (morph myz) (preserves-mult (is-monoid-morph mxy)) ⟩
                                                morph myz (morph mxy x ∙Y morph mxy y)
                                             ≡⟨ preserves-mult (is-monoid-morph myz) ⟩
                                                (morph myz (morph mxy x) ∙Z morph myz (morph mxy y))
                                             ∎) )
                              where open Monoid X using () renaming (_∙_ to _∙X_ ; ε to εX)
                                    open Monoid Y using () renaming (_∙_ to _∙Y_ ; ε to εY)
                                    open Monoid Z using () renaming (_∙_ to _∙Z_ ; ε to εZ)

 Monoid-morph-eq : {X Y : Monoid} → {m m' : Monoid-Morph X Y} → 
                  (morph m) ≡ (morph m') → m ≡ m'
 Monoid-morph-eq {X} {Y} {monoid-morph m (is-monoid-homo unit mult)} 
                         {monoid-morph .m (is-monoid-homo unit' mult')} refl = cong (λ q → monoid-morph m q) 
                                                                              (cong₂ is-monoid-homo (ir unit unit') 
                                                                                                 (iext λ x → iext (λ y → ir mult mult')))

 MonCat : Cat
 MonCat = record
      { Obj = Monoid
      ; Hom = λ M₁ M₂ → Monoid-Morph M₁ M₂
      ; iden = monoid-morph id (is-monoid-homo refl refl)
      ; _∙_ = Monoid-comp
      ; idl = Monoid-morph-eq refl
      ; idr = Monoid-morph-eq refl
      ; ass = Monoid-morph-eq refl
      }
 
--------------------------------------------------
{- Ejercicio: Dada un categoría C, definir la siguiente categoría:
  - Los objetos son morfismos de C
  - Un morfismo entre una flecha f: A → B y f': A'→ B' es un par de morfismos de C
      g1 : A → A', y g2 : B → B', tal que
                    f' ∙ g₁ ≡ g₂ ∙ f
-}

module ArrowCat (C : Cat) where

 open Cat C renaming (Obj to CObj ; Hom to CHom ; iden to Ciden ; _∙_ to _∙C_ ; idl to Cidl ; idr to Cidr ; ass to Cass)

 -- record para representar los objetos de la categoria
 record Arrow₀ : Set₁ where
   constructor arrow0
   field
      dom : CObj
      codom : CObj
      hom : CHom dom codom

 open Arrow₀ 

 -- record para representar los morfismos de la categoria
 record Arrow₁ (F F' : Arrow₀) : Set where
   constructor arrow1
   field g1 : CHom (dom F) (dom F')
         g2 : CHom (codom F) (codom F')
         is-arrowmorph : (hom F') ∙C g1 ≡ g2 ∙C (hom F)

 open Arrow₁

 Arrow-com : {X Y Z : Arrow₀} → Arrow₁ Y Z → Arrow₁ X Y → Arrow₁ X Z
 Arrow-com {X} {Y} {Z} (arrow1 g1yz g2yz pyz) (arrow1 g1xy g2xy pxy) = arrow1 (g1yz ∙C g1xy) 
                                                                              (g2yz ∙C g2xy) 
                                                                              (proof 
                                                                                 (hom Z ∙C (g1yz ∙C g1xy))
                                                                              ≡⟨ sym Cass ⟩
                                                                                 ((hom Z ∙C g1yz) ∙C g1xy)
                                                                              ≡⟨ cong (λ x → x ∙C g1xy) pyz ⟩
                                                                                 ((g2yz ∙C (hom Y)) ∙C g1xy)
                                                                              ≡⟨ Cass ⟩
                                                                                 (g2yz ∙C (hom Y ∙C g1xy))
                                                                              ≡⟨ cong (_∙C_ g2yz) pxy ⟩
                                                                                 (g2yz ∙C (g2xy ∙C (hom X)))
                                                                              ≡⟨ sym Cass ⟩
                                                                                 ((g2yz ∙C g2xy) ∙C (hom X))
                                                                              ∎)

 Arrow₁-eq : {F F' : Arrow₀} {G H : Arrow₁ F F'} → (g1 G ≡ g1 H) → (g2 G ≡ g2 H) → G ≡ H 
 Arrow₁-eq {F} {F'} {arrow1 g1G g2G pG} {arrow1 .g1G .g2G pH} refl refl = cong (arrow1 g1G g2G) (ir pG pH)

 ArrowCat : Cat
 ArrowCat = record
            { Obj = Arrow₀
            ; Hom = λ F F' → Arrow₁ F F'
            ; iden = arrow1 Ciden Ciden (trans Cidr (sym Cidl)) 
            ; _∙_ = Arrow-com
            ; idl = Arrow₁-eq Cidl Cidl
            ; idr = Arrow₁-eq Cidr Cidr
            ; ass = Arrow₁-eq Cass Cass
            }
 
--------------------------------------------------
{- Generalizamos la noción de isomorfismo de la clase pasada a cualquier categoría -}

{- Isomorfismo en una categoría -}

open Cat

record Iso {C : Cat}(A B : Obj C)(fun : Hom C A B) : Set where
  constructor iso
  field inv : Hom C B A
        law1 : _∙_ C fun inv  ≡ iden C {B}
        law2 : _∙_ C inv fun  ≡ iden C {A}

--------------------------------------------------

{- Ejercicio
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app

Sets : Cat
Sets = record
         { Obj = Set
         ; Hom = λ X Y → X → Y  
         ; iden = id
         ; _∙_ = λ f g → f ∘ g  
         ; idl = refl
         ; idr = refl
         ; ass = refl
         } 

Biyectiva : {X Y : Set}(f : X → Y) → Set
Biyectiva {X} {Y} f = (y : Y) → Σ X (λ x → (f x ≡ y) × (∀ x' → f x' ≡ y → x ≡ x')) 

-}

open import Records-completo hiding (Iso ; ext)

iso-biy : {A B : Set} → (f : A → B) → Iso {Sets} A B f → Biyectiva f 
iso-biy f (iso inv law1 law2) y = (inv y) , (cong-app law1 y) , λ x' p → proof
                                                                           inv y
                                                                         ≡⟨ cong inv (sym p) ⟩ 
                                                                           inv (f x') 
                                                                         ≡⟨ cong-app law2 x' ⟩ 
                                                                           x' 
                                                                         ∎

biy-iso : {A B : Set} → (f : A → B) → Biyectiva f → Iso {Sets} A B f 
biy-iso f biy = iso (λ b → fst (biy b)) 
                    (ext (λ b → fst (snd (biy b)) )) 
                    (ext (λ a → snd (snd (biy (f a))) a refl))




--------------------------------------------------
{- Ejercicio:
 Probar que un isormofismo en (C : Cat) es un isomorfismo en (C Op).

_Op : Cat → Cat
C Op =  let open Cat C in
        record
         { Obj = Obj
         ; Hom = λ X Y → Hom Y X 
         ; iden = iden
         ; _∙_ = λ f g → g ∙ f 
         ; idl = idr
         ; idr = idl
         ; ass = sym ass
         }

-}

c-cop : {C : Cat} → {A B : Obj C} → (fun : Hom C A B) → Iso {C} A B fun → Iso {C Op} B A fun 
c-cop fun (iso inv law1 law2) = iso inv law2 law1

cop-c : {C : Cat} → {A B : Obj C} → (fun : Hom C A B) → Iso {C Op} B A fun → Iso {C} A B fun 
cop-c fun (iso inv law1 law2) = iso inv law2 law1

--------------------------------------------------
{- Ejercicio EXTRA:
 Definir la categoría de pointed sets:
  - objetos son conjuntos junto con un elemento designado del conjunto.
     Por ejemplo (Bool , false), (ℕ , 0) , etc.
  - los morfismos son funciones entre los conjuntos que preservan el punto
     (A,a) → (B, b) es una función f : A → B, tal que f(a) = b 
-}

record PointedSet : Set₁ where
   constructor pointed
   field 
      set : Set 
      obj : set 

open PointedSet

record PointedMorph (X Y : PointedSet) : Set where
   constructor pmorph 
   field
      morph : (set X) → (set Y) 
      prop : morph (obj X) ≡ obj Y

open PointedMorph 

PointedMorph-Eq : {X Y : PointedSet} → {F G : PointedMorph X Y} → morph F ≡ morph G → F ≡ G 
PointedMorph-Eq {X} {Y} {pmorph mF pF} {pmorph .mF pG} refl = cong (pmorph mF) (ir pF pG)

PointedCat : Cat
PointedCat = record
            { Obj = PointedSet
            ; Hom = λ X Y → PointedMorph X Y
            ; iden = pmorph id refl
            ; _∙_ = λ F G → pmorph ((morph F) ∘ (morph G)) (trans (cong (morph F) (prop G)) (prop F))
            ; idl = PointedMorph-Eq refl
            ; idr = PointedMorph-Eq refl
            ; ass = PointedMorph-Eq refl
            }
--------------------------------------------------


   