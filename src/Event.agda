------------------------------------------------------------------------
-- Defines `Event` and happens-before relation `_⊏_`, proves `_⊏_` is a
-- strict partial order.
------------------------------------------------------------------------

module Event where

open import Postulates
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat
open import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_∘′_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; subst)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_; yes; no)

ProcessId = Fin n
LocalEventId = ℕ

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId

data Event : ProcessId → LocalEventId → Set where
  init : Event pid zero
  send : Message         → Event pid eid → Event pid (suc eid)
  recv : Event pid′ eid′ → Event pid eid → Event pid (suc eid)

-- To make heterogeneous equality `≅` work nicely with `Event`, we need
-- to tell Agda `Event` is injective, otherwise the unification will get
-- stuck.
-- TODO: actually prove `Event` is a injective type constructor
{-# INJECTIVE Event #-}

private
  variable
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

pid[_] : Event pid eid → ProcessId
pid[_] {pid} {eid} e = pid

eid[_] : Event pid eid → LocalEventId
eid[_] {pid} {eid} e = eid

-- We potsulate `uniquely-identify` to rule out ill-formed events that
-- couldn't happen in a valid execution.
postulate
  uniquely-identify : pid[ e ] ≡ pid[ e′ ] → eid[ e ] ≡ eid[ e′ ] → e ≅ e′

data _⊏_ : Event pid eid → Event pid′ eid′ → Set where
  processOrder₁ : e ⊏ send m e
  processOrder₂ : e ⊏ recv e′ e
  send⊏recv     : e ⊏ recv e  e′
  trans         : e ⊏ e′ → e′ ⊏ e″ → e ⊏ e″

------------------------------------------------------------------------
-- Properties about `_⊏_`, in particular, it's a strict partial order.

size : Event pid eid → ℕ
size init        = zero
size (send _ e)  = suc (size e)
size (recv e e′) = suc (size e + size e′)

⊏⇒size< : e ⊏ e′ → size e < size e′
⊏⇒size< processOrder₁ = s≤s ≤-refl
⊏⇒size< processOrder₂ = s≤s (≤-stepsˡ _ ≤-refl)
⊏⇒size< send⊏recv     = s≤s (≤-stepsʳ _ ≤-refl)
⊏⇒size< (trans x y)   = ≤-trans (⊏⇒size< x) (<⇒≤ (⊏⇒size< y))

⊏-irrefl : ¬ e ⊏ e
⊏-irrefl x = 1+n≰n (⊏⇒size< x)

⊏-trans : e ⊏ e′ → e′ ⊏ e″ → e ⊏ e″
⊏-trans = trans

⊏-asym : e ⊏ e′ → ¬ e′ ⊏ e
⊏-asym x y = ⊥-elim (⊏-irrefl (⊏-trans x y))

⊏-antisym : e ⊏ e′ → e′ ⊏ e → e ≅ e′
⊏-antisym x y = ⊥-elim (⊏-asym x y)

eid<⇒⊏-locally : pid[ e ] ≡ pid[ e′ ] → eid[ e ] < eid[ e′ ] → e ⊏ e′
eid<⇒⊏-locally {e = e} {e′ = e′@(send {eid = eidˣ} _ x)} refl y with <-cmp eid[ e ] eidˣ
... | tri< a _    _ = trans (eid<⇒⊏-locally refl a) processOrder₁
... | tri≈ _ refl _ = subst (_⊏ e′) (uniquely-identify refl refl) processOrder₁
... | tri> _ _    c = ⊥-elim (1+n≰n (≤-trans y c))
eid<⇒⊏-locally {e = e} {e′ = e′@(recv {eid = eidˣ} _ x)} refl y with <-cmp eid[ e ] eidˣ
... | tri< a _    _ = trans (eid<⇒⊏-locally refl a) processOrder₂
... | tri≈ _ refl _ = subst (_⊏ e′) (uniquely-identify refl refl) processOrder₂
... | tri> _ _    c = ⊥-elim (1+n≰n (≤-trans y c))

⊏-tri-locally : pid[ e ] ≡ pid[ e′ ] → e ⊏ e′ ⊎ e ≅ e′ ⊎ e′ ⊏ e
⊏-tri-locally {pid} {eid} {_} {pid} {eid′} {_} refl with <-cmp eid eid′
... | tri< a _ _ = inj₁ (eid<⇒⊏-locally refl a)
... | tri≈ _ b _ = inj₂ (inj₁ (uniquely-identify refl b))
... | tri> _ _ c = inj₂ (inj₂ (eid<⇒⊏-locally refl c))

≅-dec : e ≅ e′ ⊎ ¬ e ≅ e′
≅-dec {pid} {eid} {_} {pid′} {eid′} {_} with pid Fin.≟ pid′ | eid ≟ eid′
... | yes x | yes y = inj₁ (uniquely-identify x y )
... | yes x | no y  = inj₂ λ { refl → y refl }
... | no  x | _     = inj₂ λ { refl → x refl }

⊏-inv₁ : e ⊏ send m e′ → e ≅ e′ ⊎ e ⊏ e′
⊏-inv₁ processOrder₁ = inj₁ refl
⊏-inv₁ (trans x y) with ⊏-inv₁ y
... | inj₁ refl = inj₂ x
... | inj₂ z    = inj₂ (trans x z)

⊏-inv₂ : e ⊏ recv e′ e″ → (e ≅ e′ ⊎ e ⊏ e′) ⊎ (e ≅ e″ ⊎ e ⊏ e″)
⊏-inv₂ processOrder₂ = inj₂ (inj₁ refl)
⊏-inv₂ send⊏recv     = inj₁ (inj₁ refl)
⊏-inv₂ (trans x y) with ⊏-inv₂ y
... | inj₁ (inj₁ refl) = inj₁ (inj₂ x)
... | inj₁ (inj₂ z)    = inj₁ (inj₂ (trans x z))
... | inj₂ (inj₁ refl) = inj₂ (inj₂ x)
... | inj₂ (inj₂ z)    = inj₂ (inj₂ (trans x z))

⊏-dec : e ⊏ e′ ⊎ ¬ e ⊏ e′
⊏-dec {e = e} {e′ = init} = inj₂ ((λ ()) ∘′ ⊏⇒size<)
⊏-dec {e = e} {e′ = send _ e′} with ≅-dec {e = e} {e′ = e′} | ⊏-dec {e = e} {e′ = e′}
... | inj₁ refl | _      = inj₁ processOrder₁
... | inj₂ x    | inj₁ y = inj₁ (trans y processOrder₁)
... | inj₂ x    | inj₂ y = inj₂ ([ x , y ]′ ∘′ ⊏-inv₁)
⊏-dec {e = e} {e′ = recv e′ e″} with ≅-dec {e = e} {e′ = e′} | ⊏-dec {e = e} {e′ = e′} | ≅-dec {e = e} {e′ = e″} | ⊏-dec {e = e} {e′ = e″}
... | inj₁ refl | _      | _         | _      = inj₁ send⊏recv
... | _         | inj₁ y | _         | _      = inj₁ (trans y send⊏recv)
... | _         | _      | inj₁ refl | _      = inj₁ processOrder₂
... | _         | _      | _         | inj₁ w = inj₁ (trans w processOrder₂)
... | inj₂ x    | inj₂ y | inj₂ z    | inj₂ w = inj₂ ([ [ x , y ]′ , [ z , w ]′ ]′ ∘′ ⊏-inv₂)

data _⊏̸_ : Event pid eid → Event pid′ eid′ → Set where
  rule₁ : pid[ e ] ≡ pid[ e′ ] → eid[ e′ ] ≤ eid[ e ] → e ⊏̸ e′
  rule₂ : pid[ e ] ≢ pid[ e′ ] → e ≡ init → e′ ≡ init → e ⊏̸ e′
  rule₃ : pid[ e ] ≢ pid[ e′ ] → e ⊏̸ e′ → e ⊏̸ send m e′
  rule₄ : pid[ e ] ≢ pid[ e′ ] → e ⊏̸ e′ → e ⊏̸ e″ → e ⊏̸ recv e″ e′

¬⇒⊏̸₁ : pid[ e ] ≡ pid[ e′ ] → ¬ e ⊏ e′ → e ⊏̸ e′
¬⇒⊏̸₁ {pid} {eid} {e} {pid′} {eid′} {e′} x y with <-cmp eid eid′
... | tri< a _    _  = ⊥-elim (y (eid<⇒⊏-locally x a))
... | tri≈ _ refl _  = rule₁ x ≤-refl
... | tri> _ _    c  = rule₁ x (<⇒≤ c)

¬⇒⊏̸₂ : pid[ e ] ≢ pid[ e′ ] → ¬ e ⊏ e′ → e ⊏̸ e′
¬⇒⊏̸₂ {e = e} {e′ = init}       x y = {!!}
¬⇒⊏̸₂ {e = e} {e′ = send m e′}  x y with ⊏-dec {e = e} {e′ = e′}
... | inj₁ z = ⊥-elim (y (trans z processOrder₁))
... | inj₂ z = rule₃ x (¬⇒⊏̸₂ x z)
¬⇒⊏̸₂ {e = e} {e′ = recv e″ e′} x y with ⊏-dec {e = e} {e′ = e′} | ⊏-dec {e = e} {e′ = e″}
... | inj₁ z | _      = ⊥-elim (y (trans z processOrder₂))
... | _      | inj₁ w = ⊥-elim (y (trans w send⊏recv))
... | inj₂ z | inj₂ w = rule₄ x (¬⇒⊏̸₂ x z) (¬⇒⊏̸₂ {!!} w)

¬⇒⊏̸ : ¬ e ⊏ e′ → e ⊏̸ e′
¬⇒⊏̸ {pid} {_} {_} {pid′} {_} {_} with pid Fin.≟ pid′
... | yes x = ¬⇒⊏̸₁ x
... | no  x = ¬⇒⊏̸₂ x
