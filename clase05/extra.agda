module clase05.extra where
{- Ejercicio EXTRA:
 Definir la categoría cuyos
  - objetos son conjuntos finitos (y por lo tanto isomorfos a Fin n para algún n)
  - morfismos son isomorfismos.  
-}

open import Library

open import Categories

open import Categories.Iso

open import Categories.Sets

open import Data.Nat
open import Data.Fin 

record FinSet : Set₁ where
   constructor fin 
   field
      set : Set
      n : ℕ
      isof : set → Fin n
      isop : Iso (Sets {_}) isof

open FinSet 

record FinMorph (X Y : FinSet) : Set where
   constructor finmorph 
   field
      morph : (set X) → (set Y)
      isom : Iso Sets morph

open FinMorph

open Iso

FinMorph-Eq : {X Y : FinSet} → {F G : FinMorph X Y} → morph F ≅ morph G → F ≅ G 
FinMorph-Eq {X} {Y} {finmorph mF iF} {finmorph .mF iG} refl = cong (finmorph mF) (isoEq Sets iF iG)

FinSets : Cat
FinSets = record
         { Obj = FinSet
         ; Hom = λ X Y → FinMorph X Y
         ; iden = finmorph id (iso id refl refl) 
         ; _∙_ = λ F G → finmorph (morph F ∘ morph G) 
                                  (iso ((inv (isom G)) ∘ (inv (isom F))) 
                                       (ext (λ z → proof 
                                                        morph F (morph G (inv (isom G) (inv (isom F) z))) -- morph F (morph G (inv (isom G) (inv (isom F) z)))
                                                     ≅⟨ cong (morph F) (cong-app (rinv {f = morph G} (isom G)) (inv (isom F) z)) ⟩ --(cong (morph F) (rinv (isom G) (inv (isom F) z))) ⟩ 
                                                        morph F (inv (isom F) z)  -- morph F (inv (isom F) z)
                                                     ≅⟨ cong-app (rinv (isom F)) z ⟩ -- rinv (isom F) z 
                                                        z 
                                                     ∎))
                                       (ext (λ x → proof 
                                                        inv (isom G) (inv (isom F) (morph F (morph G x)))
                                                    ≅⟨ cong (inv (isom G)) (cong-app (linv (isom F)) (morph G x)) ⟩ 
                                                        inv (isom G) (morph G x) 
                                                    ≅⟨ cong-app (linv (isom G)) x ⟩
                                                        x
                                                    ∎) ))
         ; idl = FinMorph-Eq refl
         ; idr = FinMorph-Eq refl
         ; ass = FinMorph-Eq refl
         }
--------------------------------------------------

  