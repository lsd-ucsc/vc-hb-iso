------------------------------------------------------------------------
-- Defines the abstract vector clock `VCᵃ` that captures the algebraic
-- properties of the vector clock but without committing to a specific
-- representation.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _<_)

module AbstractVectorClock (n  : ℕ) (Message : Set) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (_≟_)
open import Data.Maybe using (Maybe)
open import Data.Nat.Properties using (<-cmp)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Event n Message
open import Relation.Binary using (IsStrictPartialOrder; Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_; yes; no)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId

record VCᵃ : Set₁ where
  field
    VC    : Set
    vc[_] : Event pid eid → VC
    _≈_   : VC → VC → Set
    _≺_   : VC → VC → Set
    ≺-isStrictPartialOrder : IsStrictPartialOrder _≈_ _≺_


record IsSound (vcᵃ : VCᵃ) : Set where
  open VCᵃ vcᵃ
  open IsStrictPartialOrder ≺-isStrictPartialOrder renaming (trans to ≺-trans)

  field
    rule₁ : ∀ {e : Event pid eid} {m} →
            vc[ e ] ≺ vc[ send m e ]
    rule₂ : ∀ {e : Event pid eid} {e′ : Event pid′ eid′} →
            vc[ e ] ≺ vc[ recv e′ e  ]
    rule₃ : ∀ {e : Event pid eid} {e′ : Event pid′ eid′} →
            vc[ e ] ≺ vc[ recv e  e′ ]

  soundness : ∀ {e : Event pid eid} {e′ : Event pid′ eid′} →
              e ⊏ e′ → vc[ e ] ≺ vc[ e′ ]
  soundness processOrder₁ = rule₁
  soundness processOrder₂ = rule₂
  soundness send⊏recv     = rule₃
  soundness (trans x y)   = ≺-trans (soundness x) (soundness y)


record IsComplete (vcᵃ : VCᵃ) : Set where
  open VCᵃ vcᵃ
  open IsStrictPartialOrder ≺-isStrictPartialOrder using (module Eq) renaming (irrefl to ≺-irrefl; trans to ≺-trans)

  field
    rule₁ : ∀ {e : Event pid eid} {e′ : Event pid′ eid′} →
            pid ≡ pid′ → eid < eid′ → vc[ e ] ≺ vc[ e′ ]
    rule₂ : ∀ {e : Event pid eid} →
            pid ≢ pid′ → ¬ vc[ e ] ≺ vc[ init {pid′} ]
    rule₃ : ∀ {e : Event pid eid} {e′ : Event pid′ eid′} {m : Maybe Message} →
            pid ≢ pid′ → vc[ e ] ≺ vc[ send m e′ ] → vc[ e ] ≺ vc[ e′ ]
    rule₄ : ∀ {e : Event pid eid} {e′ : Event pid′ eid′} {e″ : Event pid″ eid″} →
            pid ≢ pid′ → ¬ e ⊏ e″ → vc[ e ] ≺ vc[ recv e″ e′ ] → vc[ e ] ≺ vc[ e′ ]

  completeness₁ : ∀ {e : Event pid eid} {e′ : Event pid′ eid′} →
                  pid ≡ pid′ → vc[ e ] ≺ vc[ e′ ] → e ⊏ e′
  completeness₁ {eid = eid} {eid′ = eid′} {e = e} {e′ = e′} refl x with <-cmp eid eid′
  ... | tri< y _ _ = <⇒⊏ _ _ y
  ... | tri≈ _ y _ = ⊥-elim (≺-irrefl (subst (λ e′ → vc[ e ] ≈ vc[ e′ ]) (uniquely-identify′ e e′ y) Eq.refl) x)
  ... | tri> _ _ y = ⊥-elim (≺-irrefl Eq.refl (≺-trans (rule₁ refl y) x))

  completeness₂ : ∀ {e : Event pid eid} {e′ : Event pid′ eid′} →
        pid ≢ pid′ → vc[ e ] ≺ vc[ e′ ] → e ⊏ e′
  completeness₂ {e = e} {e′ = init}       x y = ⊥-elim (rule₂ x y)
  completeness₂ {e = e} {e′ = send m e′}  x y = trans (completeness₂ x (rule₃ x y)) processOrder₁
  completeness₂ {e = e} {e′ = recv e″ e′} x y with ⊏-dec {e = e} {e′ = e″}
  ... | inj₁ z = trans z send⊏recv
  ... | inj₂ z = trans (completeness₂ x (rule₄ x z y)) processOrder₂

  completeness : ∀ {e : Event pid eid} {e′ : Event pid′ eid′} →
                 vc[ e ] ≺ vc[ e′ ] → e ⊏ e′
  completeness {pid = pid} {pid′ = pid′} with pid ≟ pid′
  ... | yes y = completeness₁ y
  ... | no  y = completeness₂ y
