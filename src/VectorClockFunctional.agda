module VectorClockFunctional where

open import Postulates
open import Event
open import HappensBefore
open import Clock
open import Data.Bool using (true;false)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as ℕ
open import Data.Nat.Properties as NatProp
open import Data.Product using (_×_; ∃-syntax; _,_;proj₁;proj₂)
open import Data.Vec.Functional as Vector hiding (init)
open import Data.Vec.Functional.Properties as VectorProp
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as VectorEq
open import Data.Vec.Functional.Relation.Binary.Pointwise
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwiseₚ
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Function using (const)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality using (_≅_;_≇_;≅-to-≡) renaming(cong to hetero-cong)
open import Relation.Binary.PropositionalEquality using (refl;_≡_;subst;sym;cong-app;_≢_)
open import Relation.Nullary using (¬_;_because_;ofⁿ;ofʸ)

open VectorEq (DecSetoid.setoid  NatProp.≡-decSetoid)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

VC : Set
VC = Vector ℕ n

private
  variable
    vc vc′ vc″ : VC

 -- converting from Event to VC

vc[_] : Event pid eid → VC
vc[_] {pid} init        = updateAt pid (const 1) (replicate 0)
vc[_] {pid} (send _ e)  = updateAt pid suc vc[ e ]
vc[_] {pid} (recv e e′) = updateAt pid suc (zipWith _⊔_ vc[ e ] vc[ e′ ])

 -- lemmas about Vector functions

updateAt-updates-suc : ∀ m → suc (vc m) ≡ updateAt m suc vc m
updateAt-updates-suc {vc} m = sym (updateAt-updates m vc)

zip⊔-monotonicˡ : ∀ m → vc′ m ≤ zipWith _⊔_ vc′ vc m
zip⊔-monotonicˡ {vc} {vc′} m = m≤m⊔n (vc m) (vc′ m)

zip⊔-monotonicʳ : ∀ m → vc m ≤ zipWith _⊔_ vc′ vc m
zip⊔-monotonicʳ {vc} {vc′} m = m≤n⊔m (vc′ m) (vc m)

-- equalities and inequalities on VC

_≈_ : VC → VC → Set
_≈_ = _≋_

≈-refl : vc ≈ vc
≈-refl = ≋-refl

_≺_ : VC → VC → Set
vc ≺ vc′ = Pointwise _≤_ vc vc′ × ∃[ pid ] vc pid < vc′ pid

≺-irrefl : ¬ vc ≺ vc
≺-irrefl (_ , _ , x) = <-irrefl refl x

≺-trans : vc ≺ vc′ → vc′ ≺ vc″ → vc ≺ vc″
≺-trans (x , _) (y , z , w) = (λ i → ≤-trans (x i) (y i)) , z , <-transʳ (x z) w

vc[p]-<⇒≇ : ∀ pid → vc pid < vc′ pid → vc ≇ vc′
vc[p]-<⇒≇ pid vc[pid]<vc′[pid] vc≅vc′ = <⇒≢ vc[pid]<vc′[pid] (cong-app (≅-to-≡ vc≅vc′) pid)

vc-≺⇒≇ : vc ≺ vc′ → vc ≇ vc′
vc-≺⇒≇ (_ , pid , vc[pid]<vc′[pid] ) vc≅vc′ = vc[p]-<⇒≇ pid vc[pid]<vc′[pid] vc≅vc′

 -- Clock definition

clock : Clock
clock = record
  { C        = VC
  ; C[_]     = vc[_]
  ; _≈_      = _≈_
  ; ≈-refl   = ≈-refl
  ; _≺_      = _≺_
  ; ≺-irrefl = ≺-irrefl
  ; ≺-trans  = ≺-trans
  }

open ⊏-Preserving
open ⊏-Determining

clock-⊏-preserving : ⊏-Preserving clock
clock-⊏-preserving = {!!}

 -- lemmas about vc[_]

e⊏e′⇒vc[e]pid[e′]<vc[e′]pid[e′] : e ⊏ e′ →  vc[ e ] pid[ e′ ] < vc[ e′ ] pid[ e′ ]
e⊏e′⇒vc[e]pid[e′]<vc[e′]pid[e′] {e = e} {e′ = send _ e}  processOrder₁       = subst (suc (vc[ e ] pid[ e ]) ≤_) (updateAt-updates-suc pid[ e ]) ≤-refl
e⊏e′⇒vc[e]pid[e′]<vc[e′]pid[e′] {e = e} {e′ = recv e′ e} processOrder₂       = <-transʳ (zip⊔-monotonicʳ {vc[ e ]} {vc[ e′ ]} pid[ e ]) (subst (zipWith _⊔_ vc[ e′ ] vc[ e ] pid[ e ] <_) (updateAt-updates-suc pid[ e ]) (s≤s ≤-refl))
e⊏e′⇒vc[e]pid[e′]<vc[e′]pid[e′] {e = e} {e′ = recv e e′} send⊏recv           = <-transʳ (zip⊔-monotonicˡ {vc[ e ]} {vc[ e′ ]} pid[ e′ ]) (subst (zipWith _⊔_ vc[ e ] vc[ e′ ] pid[ e′ ] <_) (updateAt-updates-suc pid[ e′ ]) (s≤s ≤-refl))
e⊏e′⇒vc[e]pid[e′]<vc[e′]pid[e′] (trans {_} {_} {_} {_} {_} {_} {pid″} x x₁)  = <-transʳ (proj₁ (⊏-preserving clock-⊏-preserving x) pid″) (e⊏e′⇒vc[e]pid[e′]<vc[e′]pid[e′] x₁)

0<vc[e]pid[e] : 0 < vc[ e ] pid[ e ]
0<vc[e]pid[e] {pid} e@{e = init}    = subst (0 <_) (sym (updateAt-updates pid (replicate 0))) (s≤s z≤n)
0<vc[e]pid[e] {pid} {e = send x e}  = subst (0 <_) (sym (updateAt-updates pid vc[ e ])) (<-trans (0<vc[e]pid[e]{e = e}) (s≤s ≤-refl))
0<vc[e]pid[e] {pid} {e = recv e e′} = <-trans (<-transˡ (0<vc[e]pid[e] {e = e′}) (zip⊔-monotonicʳ {vc[ e′ ]} {vc[ e ]} pid)) ((subst (zipWith _⊔_ vc[ e ] vc[ e′ ] pid[ e′ ] <_) (updateAt-updates-suc pid[ e′ ]) (s≤s ≤-refl)))

same-p-lemma : pid[ e ] ≡ pid[ e′ ] → vc[ e ] pid[ e ] ≤ vc[ e′ ] pid[ e ] → e ⊏ e′ ⊎ e ≅ e′
same-p-lemma {e = e} {e′ = e′} pid≡ vc[e]pid[e]≤vc[e′]pid[e]
  with ⊏-tri-locally {e = e} {e′ = e′} pid≡
... | inj₁ x        = inj₁ x
... | inj₂ (inj₁ x) = inj₂ x
... | inj₂ (inj₂ y) with () ← <⇒≱ (e⊏e′⇒vc[e]pid[e′]<vc[e′]pid[e′] y) vc[e]pid[e]≤vc[e′]pid[e]

diff-p-lemma : pid[ e ] ≢ pid[ e′ ] → vc[ e ] pid[ e ] ≤ vc[ e′ ] pid[ e ] → e ⊏ e′
diff-p-lemma = {!!}

vc[init][∀p]≡0 : ∀ {pid} i → i ≢ pid → vc[ init {pid} ] i ≡ 0
vc[init][∀p]≡0 {pid} i i≢pid = updateAt-minimal i pid {const 1} (replicate 0) i≢pid

clock-⊏-determining : ⊏-Determining clock
-- ⊏-determining-rule₁ clock-⊏-determining {e = e} {e′ = e′} refl ¬e⊏e′ (∀≤ , (pid , p<p))
--   with same-p-lemma {e = e} {e′ = e′} refl (∀≤ pid[ e′ ])
-- ... | inj₁ x = ¬e⊏e′ x
-- ... | inj₂ _≅_.refl with () ← vc[p]-<⇒≇ pid p<p (hetero-cong vc[_] (_≅_.refl {x = e}))
-- ⊏-determining-rule₂ clock-⊏-determining {pid′} {init} {pid} {_} {e} x (∀≤ , ∃<)
--  with pid Fin.≟ pid′
-- ... | false because ofⁿ pid≢ = <⇒≱ (0<vc[e]pid[e] {e = e})(subst (_≥ vc[ e ] pid[ e ]) (vc[init][∀p]≡0 pid pid≢) (∀≤ pid))
-- ... | true because _ = {!!}
⊏-determining-rule₃ clock-⊏-determining {e = e} {e′ = e′} {m = m} pid≢ x y = x (⊏-preserving clock-⊏-preserving e⊏e′)
  where
    e⊏send[e′] : e ⊏ send m e′
    e⊏send[e′] = diff-p-lemma {e = e} {e′ = send m e′} pid≢ (proj₁ y pid[ e ])
    e⊏e′ : e ⊏ e′
    e⊏e′ = diff-p-⊏-inv₁ pid≢ e⊏send[e′]
⊏-determining-rule₄ clock-⊏-determining = {!!}
