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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; yes; no)

ProcessId = Fin n

LocalEventId = ℕ

data EventKind : Set where
  initᵏ : EventKind
  sendᵏ : EventKind
  recvᵏ : EventKind

data Event : ProcessId → LocalEventId → EventKind → Set where
  init : ∀ {pid} →
         Event pid zero initᵏ
  send : ∀ {pid} {eid} {kind} →
         Message →
         Event pid eid kind → Event pid (suc eid) sendᵏ
  recv : ∀ {pid pid′} {eid eid′} {kind} →
         Event pid′ eid′ sendᵏ →
         Event pid eid kind → Event pid (suc eid) recvᵏ

-- To make heterogeneous equality `≅` work nicely with `Event`, we need
-- to tell Agda `Event` is injective, otherwise the unification will get
-- stuck.
-- TODO: actually prove `Event` is a injective type constructor
{-# INJECTIVE Event #-}

private
  variable
    pid  pid′  : ProcessId
    eid  eid′  : LocalEventId
    kind kind′ : EventKind
    e  : Event pid  eid  kind
    e′ : Event pid′ eid′ kind′

pid[_] : Event pid eid kind → ProcessId
pid[_] {pid} {eid} {kind} e = pid

eid[_] : Event pid eid kind → LocalEventId
eid[_] {pid} {eid} {kind} e = eid

kind[_] : Event pid eid kind → EventKind
kind[_] {pid} {eid} {kind} e = kind

-- We potsulate `uniquely-identify` to constrain events to be from one single
-- execution.
postulate
  uniquely-identify : pid[ e ] ≡ pid[ e′ ] → eid[ e ] ≡ eid[ e′ ] → e ≅ e′

≅-dec : e ≅ e′ ⊎ ¬ e ≅ e′
≅-dec {pid} {eid} {_} {_} {pid′} {eid′} {_} {_} with pid Fin.≟ pid′ | eid ≟ eid′
... | yes x | yes y = inj₁ (uniquely-identify x y )
... | yes x | no  y = inj₂ λ { refl → y refl }
... | no  x | _     = inj₂ λ { refl → x refl }
