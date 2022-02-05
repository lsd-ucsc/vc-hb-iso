------------------------------------------------------------------------
-- Defines `Event` and happens-before relation `_⊏_`, proves `_⊏_` is a
-- strict partial order.
------------------------------------------------------------------------

open import Data.Nat as ℕ

module Event (n : ℕ) (Message : Set) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero)
open import Data.Maybe using (Maybe)
open import Data.Nat.Properties as ℕₚ
open import Data.Sum using (_⊎_)
open import Function using (_∘′_; _$′_)
open import Relation.Binary using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

ProcessId    = Fin n
LocalEventId = ℕ

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId

data Event : ProcessId → LocalEventId → Set where
  init : Event pid zero
  send : Maybe Message   → Event pid eid → Event pid (suc eid)
  recv : Event pid′ eid′ → Event pid eid → Event pid (suc eid)

private
  variable
    m  : Maybe Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

data _⊏_ : Event pid eid → Event pid′ eid′ → Set where
  processOrder₁ : e ⊏ send m e
  processOrder₂ : e ⊏ recv e′ e
  send⊏recv     : e ⊏ recv e  e′
  trans         : e ⊏ e′ → e′ ⊏ e″ → e ⊏ e″

------------------------------------------------------------------------
-- Indexed equality on events.
--
-- We could have used the heterogeneous equality `_≅_` from the standard
-- library (in `Relation.Binary.HeterogeneousEquality`) but I ran into
-- some problems while doing pattern matching on it.

data _≡ᵉ_ : Event pid eid → Event pid′ eid′ → Set where
  refl : e ≡ᵉ e

sym : e ≡ᵉ e′ → e′ ≡ᵉ e
sym refl = refl

subst : (P : ∀ {pid} {eid} → Event pid eid → Set) → e ≡ᵉ e′ → P e → P e′
subst _ refl Pe = Pe

------------------------------------------------------------------------
-- Properties about `_⊏_`, in particular, it's a strict partial order.

size : Event pid eid → ℕ
size init        = zero
size (send _ e)  = suc (size e)
size (recv e e′) = suc (size e + size e′)

⊏⇒size : e ⊏ e′ → size e < size e′
⊏⇒size processOrder₁ = s≤s ≤-refl
⊏⇒size processOrder₂ = s≤s (≤-stepsˡ _ ≤-refl)
⊏⇒size send⊏recv     = s≤s (≤-stepsʳ _ ≤-refl)
⊏⇒size (trans x y)   = ≤-trans (⊏⇒size x) (<⇒≤ (⊏⇒size y))

⊏-irrefl : ¬ e ⊏ e
⊏-irrefl x = 1+n≰n (⊏⇒size x)

⊏-trans : e ⊏ e′ → e′ ⊏ e″ → e ⊏ e″
⊏-trans = trans

⊏-asym : e ⊏ e′ → ¬ e′ ⊏ e
⊏-asym x y = ⊥-elim (⊏-irrefl (⊏-trans x y))

⊏-antisym : e ⊏ e′ → e′ ⊏ e → e ≡ᵉ e′
⊏-antisym x y = ⊥-elim (⊏-asym x y)

⊏-irrefl′ : e ≡ᵉ e′ → ¬ e ⊏ e′
⊏-irrefl′ refl = ⊏-irrefl

------------------------------------------------------------------------
-- We potsulate `uniquely-identify` to rule out ill-formed events that
-- couldn't happen in a valid execution.

postulate
  uniquely-identify : ∀ (e e′ : Event pid eid) → e ≡ᵉ e′
  ⊏-dec : ∀ (e : Event pid eid) (e′ : Event pid′ eid′) → e ⊏ e′ ⊎ ¬ e ⊏ e′

uniquely-identify′ : ∀ (e : Event pid eid) (e′ : Event pid eid′) →
                     eid ≡ eid′ → e ≡ᵉ e′
uniquely-identify′ e e′ refl = uniquely-identify e e′

init-min : ∀ (e : Event pid (suc eid)) → init {pid} ⊏ e
init-min (send _ init)         = processOrder₁
init-min (send _ e@(send _ _)) = trans (init-min e) processOrder₁
init-min (send _ e@(recv _ _)) = trans (init-min e) processOrder₁
init-min (recv _ init)         = processOrder₂
init-min (recv _ e@(send _ _)) = trans (init-min e) processOrder₂
init-min (recv _ e@(recv _ _)) = trans (init-min e) processOrder₂

-- Interestingly, this proof is really repetitive, might be a good
-- argument for tactics
<⇒⊏ : ∀ (e : Event pid eid) (e′ : Event pid eid′) → eid < eid′ → e ⊏ e′
<⇒⊏ init e@(send _ _) _ = init-min e
<⇒⊏ init e@(recv _ _) _ = init-min e
<⇒⊏ e@(send {eid = eidˣ} _ x) e′@(send {eid = eidʸ} _ y) z with <-cmp (suc eidˣ) eidʸ
... | tri< a _    _ = trans (<⇒⊏ e y a) processOrder₁
... | tri≈ _ refl _ = subst (_⊏ e′) (uniquely-identify y e) processOrder₁
... | tri> _ _    c = ⊥-elim (1+n≰n (≤-trans z c))
<⇒⊏ e@(send {eid = eidˣ }_ x) e′@(recv {eid = eidʸ} _ y) z with <-cmp (suc eidˣ) eidʸ
... | tri< a _    _ = trans (<⇒⊏ e y a) processOrder₂
... | tri≈ _ refl _ = subst (_⊏ e′) (uniquely-identify y e) processOrder₂
... | tri> _ _    c = ⊥-elim (1+n≰n (≤-trans z c))
<⇒⊏ e@(recv {eid = eidˣ} _ x) e′@(send {eid = eidʸ} _ y) z with <-cmp (suc eidˣ) eidʸ
... | tri< a _    _ = trans (<⇒⊏ e y a) processOrder₁
... | tri≈ _ refl _ = subst (_⊏ e′) (uniquely-identify y e) processOrder₁
... | tri> _ _    c = ⊥-elim (1+n≰n (≤-trans z c))
<⇒⊏ e@(recv {eid = eidˣ} _ x) e′@(recv {eid = eidʸ} _ y) z with <-cmp (suc eidˣ) eidʸ
... | tri< a _    _ = trans (<⇒⊏ e y a) processOrder₂
... | tri≈ _ refl _ = subst (_⊏ e′) (uniquely-identify y e) processOrder₂
... | tri> _ _    c = ⊥-elim (1+n≰n (≤-trans z c))

-- We can't use the `Trichotomous` from the standard library (in
-- `Relation.Binary.Definitions`) because it's defined for non-indexed
-- datatypes
⊏-trichotomous-locally : ∀ (e : Event pid eid) (e′ : Event pid eid′) →
                         Tri (e ⊏ e′) (e ≡ᵉ e′) (e′ ⊏ e)
⊏-trichotomous-locally {eid = eid} {eid′ = eid′} e e′ with <-cmp eid eid′
... | tri< a _    _ = let e⊏e′ = <⇒⊏ e e′ a
                      in tri< e⊏e′ ((_$′ e⊏e′) ∘′ ⊏-irrefl′) (⊏-asym e⊏e′)
... | tri≈ _ refl _ = let e≡ᵉe′ = uniquely-identify e e′
                      in tri≈ (⊏-irrefl′ e≡ᵉe′) e≡ᵉe′ (⊏-irrefl′ (sym e≡ᵉe′))
... | tri> _ _    c = let e′⊏e = <⇒⊏ e′ e c
                      in tri> (⊏-asym e′⊏e) ((_$′ e′⊏e) ∘′ ⊏-irrefl′ ∘′ sym) e′⊏e
