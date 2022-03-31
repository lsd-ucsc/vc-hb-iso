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

-- Reflecting

ClockCompare = ∀ {pid pid′} {eid eid′} → Event pid eid → Event pid′ eid′ → Set

module _ (_≺_ : ClockCompare) where

   ⊏-Reflecting : Set
   ⊏-Reflecting = ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
                   e ≺ e′ → e ⊏ e′

   ⊏-ReflectingRule = ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
                   e ⊏̸ e′ → ¬ e ≺ e′

   ⊏-ReflectingRule-sufficient : ⊏-ReflectingRule → ⊏-Reflecting
   ⊏-ReflectingRule-sufficient x {e = e} {e′ = e′} y with ⊏-dec {e = e} {e′ = e′} 
   ... | inj₁ z = z
   ... | inj₂ z = ⊥-elim (x (¬⇒⊏̸ z) y)
   
   ⊏-ReflectingRules-necessary : ⊏-Reflecting → ⊏-ReflectingRule
   ⊏-ReflectingRules-necessary x y z = ⊏̸⇒¬ y (x z)
