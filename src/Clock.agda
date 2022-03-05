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

record ClockCompare : Set₁ where
  field
    _≺_      : Event pid eid → Event pid′ eid′ → Set
    ≺-irrefl : ¬ e ≺ e


module _ (c : ClockCompare) where
  open ClockCompare c

  ⊏-Determining : Set
  ⊏-Determining = ∀ {pid pid′} {eid eid′} {e : Event pid eid} {e′ : Event pid′ eid′} →
                  e ≺ e′ → e ⊏ e′

  record ⊏-DeterminingRules : Set where
    field
      ⊏-determining-local : pid[ e ] ≡ pid[ e′ ] → e′ ⊏ e → ¬ e ≺ e′ 
      ⊏-determining-init  : pid[ e ] ≢ pid[ e′ ] → e′ ≡ init → ¬ e ≺ e′ 
      ⊏-determining-send  : pid[ e ] ≢ pid[ e′ ] → e ≺ send m e′ → e ≺ e′
      ⊏-determining-recv  : pid[ e ] ≢ pid[ e′ ] → e ≺ recv e″ e′ → e ≺ e′ ⊎ e ≺ e″ ⊎ e ≅ e″
      
    ⊏-determining₁ : pid[ e ] ≢ pid[ e′ ] →  e ≺ e′ → e ⊏ e′
    ⊏-determining₁ {e = e} {e′ = init}        x y = ⊥-elim (⊏-determining-init x refl y)
    ⊏-determining₁ {e = e} {e′ = send m e′}   x y = trans (⊏-determining₁ x (⊏-determining-send x y)) processOrder₁
    ⊏-determining₁ {e = e} {e′ = recv e″ e′} x y with ⊏-determining-recv x y
    ... | inj₁ z = trans (⊏-determining₁ x z) processOrder₂
    ... | inj₂ (inj₂ refl) = send⊏recv
    ... | inj₂ (inj₁ z) with pid[ e ] ≟ pid[ e″ ]
    ...    | no  w    = trans (⊏-determining₁ w z) send⊏recv
    ...    | yes refl with ⊏-tri-locally {e = e} {e′ = e″} refl 
    ...         | inj₁ v = trans v send⊏recv
    ...         | inj₂ (inj₁ refl) = send⊏recv
    ...         | inj₂ (inj₂ v) = ⊥-elim (⊏-determining-local refl v z)
   
  open ⊏-DeterminingRules

  ⊏-DetermingRules-sufficient : ⊏-DeterminingRules → ⊏-Determining
  ⊏-DetermingRules-sufficient rules {e = e} {e′ = e′} x with pid[ e ] ≟ pid[ e′ ]
  ... | no  pid≢ = ⊏-determining₁ rules pid≢ x
  ... | yes refl with ⊏-tri-locally {e = e} {e′ = e′} refl
  ...         | inj₁ y           = y
  ...         | inj₂ (inj₁ refl) = ⊥-elim (≺-irrefl x)
  ...         | inj₂ (inj₂ y)    = ⊥-elim (⊏-determining-local rules refl y x)

  postulate
      ⊏-preserving : e ⊏ e′ → e ≺ e′
      
  ⊏-DeterminingRules-necessary : ⊏-Determining → ⊏-DeterminingRules
  ⊏-determining-local (⊏-DeterminingRules-necessary x) y z w   = ⊏-asym (x w) z
  ⊏-determining-init (⊏-DeterminingRules-necessary x) y refl w = ¬e⊏init refl (x w)
  ⊏-determining-send (⊏-DeterminingRules-necessary x) y z with ⊏-inv₁ (x z)
  ... | inj₁ refl = ⊥-elim (y refl)
  ... | inj₂ y₁ = ⊏-preserving y₁
  ⊏-determining-recv  (⊏-DeterminingRules-necessary x) y z with ⊏-inv₂ (x z)
  ... | inj₁ (inj₁ w) = inj₂ (inj₂ w)
  ... | inj₁ (inj₂ w) = inj₂ (inj₁ (⊏-preserving w))
  ... | inj₂ (inj₁ refl) = ⊥-elim (y refl)
  ... | inj₂ (inj₂ w) = inj₁ (⊏-preserving w)
