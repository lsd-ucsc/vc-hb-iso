------------------------------------------------------------------------
-- History-carrying events.
------------------------------------------------------------------------

module Event where

open import Postulates
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat
open import Data.Nat.Properties as ℕₚ
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_; yes; no)

ProcessId = Fin n

LocalEventId = ℕ

data Event : ProcessId → LocalEventId → Set where
  init : ∀ {pid} →
         Event pid zero
  send : ∀ {pid} {eid} →
         Message →
         Event pid eid → Event pid (suc eid)
  recv : ∀ {pid pid′} {eid eid′} →
         Event pid′ eid′ → 
         Event pid eid → Event pid (suc eid)

-- To make heterogeneous equality `≅` work nicely with `Event`, we need
-- to tell Agda `Event` is injective, otherwise the unification will get
-- stuck.
-- TODO: actually prove `Event` is a injective type constructor
{-# INJECTIVE Event #-}

private
  variable
    pid pid′ : ProcessId
    eid eid′ : LocalEventId
    e  : Event pid  eid
    e′ : Event pid′ eid′

pid[_] : Event pid eid → ProcessId
pid[_] {pid} {eid} e = pid

eid[_] : Event pid eid → LocalEventId
eid[_] {pid} {eid} e = eid

-- We potsulate `uniquely-identify` to constrain events to be from the
-- same execution.
postulate
  uniquely-identify : pid[ e ] ≡ pid[ e′ ] → eid[ e ] ≡ eid[ e′ ] → e ≅ e′

≅-dec : e ≅ e′ ⊎ ¬ e ≅ e′
≅-dec {pid} {eid} {_} {pid′} {eid′} {_} with pid Fin.≟ pid′ | eid ≟ eid′
... | yes x | yes y = inj₁ (uniquely-identify x y )
... | yes x | no  y = inj₂ λ { refl → y refl }
... | no  x | _     = inj₂ λ { refl → x refl }

