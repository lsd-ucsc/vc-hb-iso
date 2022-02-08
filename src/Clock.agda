------------------------------------------------------------------------
-- TODO
------------------------------------------------------------------------

module Clock  where

open import Postulates
open import Event
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (_≟_)
open import Data.Maybe using (Maybe)
open import Data.Nat as Nat
open import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_; yes; no)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

record Clock : Set₁ where
  field
    C        : Set
    C[_]     : Event pid eid → C
    _≈_      : C → C → Set
    ≈-refl   : ∀ {c} → c ≈ c
--  ≈-trans  : ∀ {c c′ c″} → c ≈ c′ → c′ ≈ c″ → c ≈ c″
--  ≈-sym    : ∀ {c c′} → c ≈ c′ → c′ ≈ c
    _≺_      : C → C → Set
    ≺-irrefl : ∀ {c} → ¬ c ≺ c
    ≺-trans  : ∀ {c c′ c″} → c ≺ c′ → c′ ≺ c″ → c ≺ c″


record ⊏-Preserving (clock : Clock) : Set where
  open Clock clock

  field
    ⊏-preserving-rule₁ : C[ e ] ≺ C[ send m e ]
    ⊏-preserving-rule₂ : C[ e ] ≺ C[ recv e′ e″ ]
    ⊏-preserving-rule₃ : C[ e ] ≺ C[ recv e′ e″ ]

  ⊏-preserving : e ⊏ e′ → C[ e ] ≺ C[ e′ ]
  ⊏-preserving processOrder₁ = ⊏-preserving-rule₁
  ⊏-preserving processOrder₂ = ⊏-preserving-rule₂
  ⊏-preserving send⊏recv     = ⊏-preserving-rule₃
  ⊏-preserving (trans x y)   = ≺-trans (⊏-preserving x) (⊏-preserving y)


record ⊏-Determining (clock : Clock) : Set where
  open Clock clock

  field
    ⊏-determining-rule₁ : pid[ e ] ≡ pid[ e′ ] → ¬ e ⊏ e′ → ¬ C[ e ] ≺ C[ e′ ]
    ⊏-determining-rule₂ : e′ ≡ init → ¬ C[ e ] ≺ C[ e′ ]
    ⊏-determining-rule₃ : pid[ e ] ≢ pid[ e′ ] → ¬ C[ e ] ≺ C[ e′ ] → ¬ C[ e ] ≺ C[ send m e′ ]
    ⊏-determining-rule₄ : pid[ e ] ≢ pid[ e′ ] → ¬ C[ e ] ≺ C[ e′ ] → ¬ C[ e ] ≺ C[ e″ ] → ¬ C[ e ] ≺ C[ recv e″ e′ ]    

  ⊏-determining-contra : ¬ e ⊏ e′ → ¬ C[ e ] ≺ C[ e′ ]
  ⊏-determining-contra {pid} {eid} {e} {pid′} {eid′} {init}       x = ⊏-determining-rule₂ refl
  ⊏-determining-contra {pid} {eid} {e} {pid′} {eid′} {send _  e′} x with pid Fin.≟ pid′ | ⊏-dec {e = e} {e′ = e′}
  ... | yes y | _      = ⊏-determining-rule₁ y x
  ... | no  y | inj₁ z = ⊥-elim (x (⊏-trans z processOrder₁))
  ... | no  y | inj₂ z = ⊏-determining-rule₃ y (⊏-determining-contra z)  
  ⊏-determining-contra {pid} {eid} {e} {pid′} {eid′} {recv e″ e′} x with pid Fin.≟ pid′ | ⊏-dec {e = e} {e′ = e′} | ⊏-dec {e = e} {e′ = e″}
  ... | yes y | _      | _      = ⊏-determining-rule₁ y x
  ... | no  y | inj₁ z | _      = ⊥-elim (x (⊏-trans z processOrder₂))
  ... | no  y | _      | inj₁ w = ⊥-elim (x (⊏-trans w send⊏recv))  
  ... | no  y | inj₂ z | inj₂ w = ⊏-determining-rule₄ y (⊏-determining-contra z) (⊏-determining-contra w)

  ⊏-determining : C[ e ] ≺ C[ e′ ] → e ⊏ e′
  ⊏-determining {e = e} {e′ = e′} x with ⊏-dec {e = e} {e′ = e′}
  ... | inj₁ y = y
  ... | inj₂ y = ⊥-elim (⊏-determining-contra y x)
