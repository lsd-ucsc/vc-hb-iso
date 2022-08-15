module VectorClockFunctional where

open import Postulates
open import Event
open import HappensBefore

open import Data.Bool using (true;false)
open import Data.Empty using (⊥-elim)
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
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.Definitions using (_Respectsʳ_)
open import Relation.Binary.HeterogeneousEquality using (refl;_≅_;_≇_;≅-to-≡) renaming(cong to hetero-cong;subst to hetero-subst)
open import Relation.Binary.PropositionalEquality as Eq using (refl;_≡_;subst;sym;cong;cong-app;_≢_)
open import Relation.Nullary using (¬_;_because_;ofⁿ;ofʸ;yes;no)

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
vc[_] {pid} init        = updateAt pid suc (replicate 0)
vc[_] {pid} (send _ e)  = updateAt pid suc vc[ e ]
vc[_] {pid} (recv e′ e) = updateAt pid suc (zipWith _⊔_ vc[ e′ ] vc[ e ])

 -- lemmas about _≤_
 
≤-respʳ-≡ : _≤_ Respectsʳ _≡_
≤-respʳ-≡ = subst (_ ≤_)

 -- lemmas about Vector functions

updateAt-updates-suc : ∀ m → suc (vc m) ≡ updateAt m suc vc m
updateAt-updates-suc {vc} m = sym (updateAt-updates m vc)

zip⊔-monotonicˡ : ∀ (vc : VC) (vc′ : VC) m → vc′ m ≤ zipWith _⊔_ vc′ vc m
zip⊔-monotonicˡ vc vc′ m = m≤m⊔n (vc′ m) (vc m)

zip⊔-monotonicʳ : ∀ (vc : VC) (vc′ : VC) m  → vc m ≤ zipWith _⊔_ vc′ vc m
zip⊔-monotonicʳ vc vc′ m = m≤n⊔m (vc′ m) (vc m)

 -- lemmas about VC

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

 -- lemmas about vc[_]

join-self-index-< : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′)
                                       → vc[ e ] pid[ e′ ] ⊔ vc[ e′ ] pid[ e′ ] < vc[ recv e e′ ] pid[ e′ ]
join-self-index-< e e′ = ≤-respʳ-≡ (updateAt-updates-suc pid[ e′ ]) ≤-refl

recv-others-index-< : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′)
                             → vc[ e ] pid[ e′ ] < vc[ recv e e′ ] pid[ e′ ]
recv-others-index-< e e′ = <-transʳ (zip⊔-monotonicˡ vc[ e′ ] vc[ e ] pid[ e′ ]) (join-self-index-< e e′)

recv-self-index-< : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′)
                              → vc[ e′ ] pid[ e′ ] < vc[ recv e e′ ] pid[ e′ ]
recv-self-index-< e e′ = <-transʳ (zip⊔-monotonicʳ vc[ e′ ] vc[ e ]  pid[ e′ ]) (join-self-index-< e e′)

send-self-index-< : ∀ {pid eid} (e : Event pid eid) m
                          → vc[ e ] pid[ e ] < vc[ send m e ] pid[ e ] 
send-self-index-< e _ = ≤-respʳ-≡ (updateAt-updates-suc pid[ e ]) ≤-refl

init-self-index-≡ : ∀ {pid} → vc[ init {pid} ] pid ≡ 1
init-self-index-≡ {pid} = updateAt-updates pid (replicate 0)

recv-others-index : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′) i  → i ≢ pid[ e′ ] →  (zipWith _⊔_ vc[ e ] vc[ e′ ]) i ≡ vc[ recv e e′ ] i
recv-others-index e e′ i i≢pid = sym (updateAt-minimal i pid[ e′ ] (zipWith _⊔_ vc[ e ] vc[ e′ ]) i≢pid)
recv-others-index-≤ʳ : ∀ {pid pid′ eid eid′}(e : Event pid eid) (e′ : Event pid′ eid′) i
                                → i ≢ pid[ e′ ] → vc[ e′ ] i ≤ vc[ recv e e′ ] i
recv-others-index-≤ʳ e e′ i i≢pid = ≤-respʳ-≡ (recv-others-index e e′ i i≢pid ) (zip⊔-monotonicʳ vc[ e′ ] vc[ e ] i)

recv-others-index-≤ˡ : ∀ {pid pid′ eid eid′}(e : Event pid eid) (e′ : Event pid′ eid′) i
                               → i ≢ pid[ e′ ] → vc[ e ] i ≤ vc[ recv e e′ ] i
recv-others-index-≤ˡ e e′ i i≢pid = ≤-respʳ-≡ (recv-others-index e e′ i i≢pid) ((zip⊔-monotonicˡ vc[ e′ ] vc[ e ] i))

send-others-index-≡ : ∀{pid eid } (e : Event pid eid) m i
                            → i ≢ pid[ e ] → vc[ send m e ] i ≡ vc[ e ] i
send-others-index-≡ e _ i i≢pid = updateAt-minimal i pid[ e ] vc[ e ] i≢pid

init-others-index-≡ : ∀ {pid} i → i ≢ pid → vc[ init {pid} ] i ≡ 0
init-others-index-≡ {pid} i i≢pid = updateAt-minimal i pid (replicate 0) i≢pid

merge-others-indexʳ-≡ : pid[ e ] ≢ pid[ e′ ] → vc[ e″ ] pid[ e ] < vc[ e′ ] pid[ e ] → vc[ recv e″ e′ ] pid[ e ] ≡ vc[ e′ ] pid[ e ]
merge-others-indexʳ-≡ {e = e} {e′ = e′} {e″ = e″} x y = Eq.trans (sym (recv-others-index e″ e′ pid[ e ] x)) (m≤n⇒m⊔n≡n (<⇒≤ y))

merge-others-indexˡ-≡ : pid[ e ] ≢ pid[ e′ ] → ¬ (vc[ e″ ] pid[ e ] < vc[ e′ ] pid[ e ]) → vc[ recv e″ e′ ] pid[ e ] ≡ vc[ e″ ] pid[ e ]
merge-others-indexˡ-≡ {e = e} {e′ = e′} {e″ = e″} x y =  Eq.trans (sym (recv-others-index e″ e′ pid[ e ] x)) (m≥n⇒m⊔n≡m (≮⇒≥ y))

0<vc[e]pid[e] : 0 < vc[ e ] pid[ e ]
0<vc[e]pid[e] {pid} e@{e = init}    = subst (0 <_) (sym init-self-index-≡) (s≤s z≤n)
0<vc[e]pid[e] {pid} {e = send x e}  = subst (0 <_) (sym (updateAt-updates pid vc[ e ])) (<-trans (0<vc[e]pid[e]{e = e}) (s≤s ≤-refl))
0<vc[e]pid[e] {pid} {e = recv e′ e} = <-trans (<-transˡ (0<vc[e]pid[e] {e = e}) (zip⊔-monotonicʳ vc[ e ] vc[ e′ ] pid)) (join-self-index-< e′ e)

-- main theorems

≺-preserves-⊏ : e ⊏ e′ →  vc[ e ] ≺ vc[ e′ ]
≺-preserves-⊏ {e = e} {e′ = send m e} processOrder₁ = lemma , pid[ e ] , send-self-index-< e m
  where
   lemma : Pointwise _≤_ vc[ e ] vc[ send m e ]
   lemma i with i Fin.≟ pid[ e ]
   ... | yes x rewrite x  = <⇒≤ (send-self-index-< e m)
   ... | no x rewrite send-others-index-≡ e m i x = ≤-refl 
≺-preserves-⊏ {e = e} {e′ = recv e″ e} processOrder₂ = lemma , pid[ e ] , (recv-self-index-< e″ e)
  where
   lemma : Pointwise _≤_ vc[ e ] vc[ recv e″ e ]
   lemma i with i Fin.≟ pid[ e ]
   ... | yes x rewrite x  = <⇒≤ (recv-self-index-< e″ e ) 
   ... | no x = recv-others-index-≤ʳ e″ e i x
≺-preserves-⊏ {e = e} {e′ = recv e e″} send⊏recv = lemma , pid[ e″ ] , recv-others-index-< e e″
  where
   lemma : Pointwise _≤_ vc[ e ] vc[ recv e e″ ]
   lemma i with i Fin.≟ pid[ e″ ]
   ... | yes x rewrite x  = <⇒≤ (recv-others-index-< e e″)
   ... | no x = recv-others-index-≤ˡ e e″ i x
≺-preserves-⊏ {e = e} {e′ = e′} (trans x x₁) = ≺-trans (≺-preserves-⊏ x) (≺-preserves-⊏ x₁)

-- other lemmas about vc[_]

≺-preserves-⊏-index : e ⊏ e′ →  vc[ e ] pid[ e′ ] < vc[ e′ ] pid[ e′ ]
≺-preserves-⊏-index {e = e} {e′ = send m e}  processOrder₁       = send-self-index-< e m
≺-preserves-⊏-index {e = e} {e′ = recv e′ e} processOrder₂      = recv-self-index-< e′ e
≺-preserves-⊏-index {e = e} {e′ = recv e e′} send⊏recv          = recv-others-index-< e e′
≺-preserves-⊏-index (trans {_} {_} {_} {_} {_} {_} {pid″} x y)  = <-transʳ ((proj₁ (≺-preserves-⊏ x)  pid″)) (≺-preserves-⊏-index y)

_≺⁻_ : Event pid eid → Event pid′ eid′ → Set
_≺⁻_  e e′ = vc[ e ] pid[ e ] ≤ vc[ e′ ] pid[ e ] × e ≇ e′

≺⁻-irrefl : ¬ e ≺⁻ e
≺⁻-irrefl (_ , x) = x refl

≺⇒≺⁻ : vc[ e ] ≺ vc[ e′ ] → e ≺⁻ e′
≺⇒≺⁻ {e = e} (∀≤ , p , p<) = (∀≤ pid[ e ]) , λ{refl → <⇒≢ p< refl}

⊏̸⇒¬≺⁻ : e ⊏̸ e′ → ¬ (e ≺⁻ e′)
⊏̸⇒¬≺⁻ (⊏̸-eid {e = e} {e′ = e′} x y) (z , w) with m≤n⇒m<n∨m≡n y
... | inj₁ u = <⇒≱ (≺-preserves-⊏-index {e = e′} {e′ = e} (eid<⇒⊏-locally (sym x) u )) z
... | inj₂ u = w (uniquely-identify x (sym u))
⊏̸⇒¬≺⁻ (⊏̸-init {e = e} x refl) (z , _) = <⇒≱ ((0<vc[e]pid[e] {e = e})) (subst ( vc[ e ] pid[ e ] ≤_) ((init-others-index-≡ pid[ e ] x)) z)
⊏̸⇒¬≺⁻ (⊏̸-send {e = e} {e′ = e′} {m = m} x y) (z , _) = ⊏̸⇒¬≺⁻ y (≤-respʳ-≡ ((send-others-index-≡ e′ m pid[ e ] x)) z , (λ {refl → x refl}))
⊏̸⇒¬≺⁻ (⊏̸-recv  {e = e} {e′ = e′} {e″ = e″} x y z w) (u , _)
   with vc[ e″ ] pid[ e ] <? vc[ e′ ] pid[ e ]
... | yes v = ⊏̸⇒¬≺⁻ y ((≤-respʳ-≡ (merge-others-indexʳ-≡ {e = e} {e′ = e′} {e″ = e″} x v) u) , (λ {refl → x refl}))
... | no  v  with ≅-dec {e = e} {e′ = e″}
...           | inj₁ t = w t
...           | inj₂ t = ⊏̸⇒¬≺⁻ z ((≤-respʳ-≡ (merge-others-indexˡ-≡ {e = e} {e′ = e′} {e″ = e″} x v) u) , t)

≺-reflects-⊏ : vc[ e ] ≺ vc[ e′ ] → e ⊏ e′
≺-reflects-⊏ {e = e} {e′ = e′} x with ⊏-dec {e = e} {e′ = e′}
... | inj₁ z = z
... | inj₂ z = ⊥-elim ((⊏̸⇒¬≺⁻ (¬⇒⊏̸ z)) (≺⇒≺⁻ x))
