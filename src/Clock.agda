------------------------------------------------------------------------
-- Generic clock interface.
------------------------------------------------------------------------

module Clock where

open import Postulates
open import Event
open import HappensBefore
open import Data.Empty using (⊥-elim)
open import Data.Fin using(_≟_)
open import Data.Nat using (ℕ;_≤_;_≰_;_<_)
open import Data.Nat.Properties using (<⇒≱)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Relation.Binary.HeterogeneousEquality using (_≇_;refl;_≅_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_;refl)
open import Relation.Nullary using (¬_;yes;no)
open import Relation.Nullary.Negation using (contraposition)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

 -- Preserving
record Clock : Set₁ where
  field
    C        : Set
    C[_]     : Event pid eid → C
    _≺_      : C → C → Set
    ≺-trans  : ∀ {c c′ c″} → c ≺ c′ → c′ ≺ c″ → c ≺ c″


module _ (clock : Clock) where
  open Clock clock

  ⊏-Preserving : Set
  ⊏-Preserving = ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
                 e ⊏ e′ → C[ e ] ≺ C[ e′ ]

  record ⊏-PreservingRules : Set where
    field
      ⊏-preserving-rule₁ : C[ e ] ≺ C[ send m e ]
      ⊏-preserving-rule₂ : C[ e ] ≺ C[ recv e′ e  ]
      ⊏-preserving-rule₃ : C[ e ] ≺ C[ recv e  e′ ]

  open ⊏-PreservingRules
  
  ⊏-PreservingRules-sufficient : ⊏-PreservingRules → ⊏-Preserving
  ⊏-PreservingRules-sufficient rules processOrder₁ = ⊏-preserving-rule₁ rules
  ⊏-PreservingRules-sufficient rules processOrder₂ = ⊏-preserving-rule₂ rules
  ⊏-PreservingRules-sufficient rules send⊏recv     = ⊏-preserving-rule₃ rules
  ⊏-PreservingRules-sufficient rules (trans x y)   = ≺-trans (⊏-PreservingRules-sufficient rules x) (⊏-PreservingRules-sufficient rules y)

  ⊏-PreservingRules-necessary : ⊏-Preserving → ⊏-PreservingRules
  ⊏-preserving-rule₁ (⊏-PreservingRules-necessary x) = x processOrder₁
  ⊏-preserving-rule₂ (⊏-PreservingRules-necessary x) = x processOrder₂
  ⊏-preserving-rule₃ (⊏-PreservingRules-necessary x) = x send⊏recv

 -- Determining
 
record ClockCompare : Set₁ where
  field
    _≺_      : Event pid eid → Event pid′ eid′ → Set
    ≺-irrefl : ¬ e ≺ e


module _ (c : ClockCompare) where
  open ClockCompare c

  ⊏-Reflecting : Set
  ⊏-Reflecting = ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
                  e ≺ e′ → e ⊏ e′

  record ⊏-ReflectingRules : Set where
    field
      ⊏-reflecting-local : pid[ e ] ≡ pid[ e′ ] → e′ ⊏ e → ¬ e ≺ e′ 
      ⊏-reflecting-init  : pid[ e ] ≢ pid[ e′ ] → e′ ≡ init → ¬ e ≺ e′ 
      ⊏-reflecting-send  : pid[ e ] ≢ pid[ e′ ] → e ≺ send m e′ → e ≺ e′
      ⊏-reflecting-recv  : pid[ e ] ≢ pid[ e′ ] → e ≺ recv e″ e′ → e ≺ e′ ⊎ e ≺ e″ ⊎ e ≅ e″
      
    ⊏-reflecting₁ : pid[ e ] ≢ pid[ e′ ] →  e ≺ e′ → e ⊏ e′
    ⊏-reflecting₁ {e = e} {e′ = init}        x y = ⊥-elim (⊏-reflecting-init x refl y)
    ⊏-reflecting₁ {e = e} {e′ = send m e′}   x y = trans (⊏-reflecting₁ x (⊏-reflecting-send x y)) processOrder₁
    ⊏-reflecting₁ {e = e} {e′ = recv e″ e′} x y with ⊏-reflecting-recv x y
    ... | inj₁ z = trans (⊏-reflecting₁ x z) processOrder₂
    ... | inj₂ (inj₂ refl) = send⊏recv
    ... | inj₂ (inj₁ z) with pid[ e ] ≟ pid[ e″ ]
    ...    | no  w    = trans (⊏-reflecting₁ w z) send⊏recv
    ...    | yes refl with ⊏-tri-locally {e = e} {e′ = e″} refl 
    ...         | inj₁ v = trans v send⊏recv
    ...         | inj₂ (inj₁ refl) = send⊏recv
    ...         | inj₂ (inj₂ v) = ⊥-elim (⊏-reflecting-local refl v z)
   
  open ⊏-ReflectingRules

  ⊏-ReflectingRules-sufficient : ⊏-ReflectingRules → ⊏-Reflecting
  ⊏-ReflectingRules-sufficient rules {e = e} {e′ = e′} x with pid[ e ] ≟ pid[ e′ ]
  ... | no  pid≢ = ⊏-reflecting₁ rules pid≢ x
  ... | yes refl with ⊏-tri-locally {e = e} {e′ = e′} refl
  ...         | inj₁ y           = y
  ...         | inj₂ (inj₁ refl) = ⊥-elim (≺-irrefl x)
  ...         | inj₂ (inj₂ y)    = ⊥-elim (⊏-reflecting-local rules refl y x)

  postulate
      ⊏-preserving : e ⊏ e′ → e ≺ e′
      
  ⊏-ReflectingRules-necessary : ⊏-Reflecting → ⊏-ReflectingRules
  ⊏-reflecting-local (⊏-ReflectingRules-necessary x) y z w   = ⊏-asym (x w) z
  ⊏-reflecting-init (⊏-ReflectingRules-necessary x) y refl w = ¬e⊏init refl (x w)
  ⊏-reflecting-send (⊏-ReflectingRules-necessary x) y z with ⊏-inv₁ (x z)
  ... | inj₁ refl = ⊥-elim (y refl)
  ... | inj₂ y₁ = ⊏-preserving y₁
  ⊏-reflecting-recv  (⊏-ReflectingRules-necessary x) y z with ⊏-inv₂ (x z)
  ... | inj₁ (inj₁ w) = inj₂ (inj₂ w)
  ... | inj₁ (inj₂ w) = inj₂ (inj₁ (⊏-preserving w))
  ... | inj₂ (inj₁ refl) = ⊥-elim (y refl)
  ... | inj₂ (inj₂ w) = inj₁ (⊏-preserving w)
