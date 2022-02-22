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
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality using (refl;_≅_;_≇_;≅-to-≡) renaming(cong to hetero-cong;subst to hetero-subst)
open import Relation.Binary.PropositionalEquality using (refl;_≡_;subst;sym;cong;cong-app;_≢_)
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
vc[_] {pid} init        = updateAt pid (const 1) (replicate 0)
vc[_] {pid} (send _ e)  = updateAt pid suc vc[ e ]
vc[_] {pid} (recv e e′) = updateAt pid suc (zipWith _⊔_ vc[ e ] vc[ e′ ])

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

vc[e]pid⊔bv[e′]pid<vc[recv[e,e′]]pid : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′) → vc[ e ] pid[ e′ ] ⊔ vc[ e′ ] pid[ e′ ] < vc[ recv e e′ ] pid[ e′ ]
vc[e]pid⊔bv[e′]pid<vc[recv[e,e′]]pid e e′ = subst (vc[ e ] pid[ e′ ] ⊔ vc[ e′ ] pid[ e′ ] <_) (updateAt-updates-suc pid[ e′ ]) ≤-refl

vc[e]pid<vc[recv[e,e′]]pid : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′) → vc[ e ] pid[ e′ ] < vc[ recv e e′ ] pid[ e′ ]
vc[e]pid<vc[recv[e,e′]]pid e e′ = <-transʳ (zip⊔-monotonicˡ vc[ e′ ] vc[ e ] pid[ e′ ]) (vc[e]pid⊔bv[e′]pid<vc[recv[e,e′]]pid e e′)

vc[e′]pid<vc[recv[e,e′]]pid : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′) → vc[ e′ ] pid[ e′ ] < vc[ recv e e′ ] pid[ e′ ]
vc[e′]pid<vc[recv[e,e′]]pid e e′ = <-transʳ (zip⊔-monotonicʳ vc[ e′ ] vc[ e ]  pid[ e′ ]) (vc[e]pid⊔bv[e′]pid<vc[recv[e,e′]]pid e e′)

vc[e]pid<vc[send[e]]pid : ∀ {pid eid} (e : Event pid eid) m → vc[ e ] pid[ e ] < vc[ send m e ] pid[ e ] 
vc[e]pid<vc[send[e]]pid e _ = subst (vc[ e ] pid[ e ] <_) (updateAt-updates-suc pid[ e ]) ≤-refl

vc[init]pid≡1 : ∀ {pid} → vc[ init {pid} ] pid ≡ 1
vc[init]pid≡1 {pid} = updateAt-updates pid (replicate 0)

pid≢i⇒vc[e]⊔vc[e′]i≡vc[recv[e,e′]]i : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′) i → i ≢ pid[ e′ ] →  (zipWith _⊔_ vc[ e ] vc[ e′ ]) i ≡ vc[ recv e e′ ] i
pid≢i⇒vc[e]⊔vc[e′]i≡vc[recv[e,e′]]i e e′ i i≢pid = sym (updateAt-minimal i pid[ e′ ] (zipWith _⊔_ vc[ e ] vc[ e′ ]) i≢pid)

pid≢i⇒vc[e′]i≤vc[recv[e,e′]]i : ∀ {pid pid′ eid eid′}(e : Event pid eid) (e′ : Event pid′ eid′) i → i ≢ pid[ e′ ] → vc[ e′ ] i ≤ vc[ recv e e′ ] i
pid≢i⇒vc[e′]i≤vc[recv[e,e′]]i e e′ i i≢pid = subst ( vc[ e′ ] i ≤_) (pid≢i⇒vc[e]⊔vc[e′]i≡vc[recv[e,e′]]i e e′ i i≢pid ) (zip⊔-monotonicʳ vc[ e′ ] vc[ e ] i)

pid≢i⇒vc[e]i≤vc[recv[e,e′]]i : ∀ {pid pid′ eid eid′}(e : Event pid eid) (e′ : Event pid′ eid′) i → i ≢ pid[ e′ ] → vc[ e ] i ≤ vc[ recv e e′ ] i
pid≢i⇒vc[e]i≤vc[recv[e,e′]]i e e′ i i≢pid = subst (vc[ e ] i ≤_) (pid≢i⇒vc[e]⊔vc[e′]i≡vc[recv[e,e′]]i e e′ i i≢pid) ((zip⊔-monotonicˡ vc[ e′ ] vc[ e ] i))

pid≢i⇒vc[send[e]]i≡vc[e]i : ∀{pid eid } (e : Event pid eid) m i → i ≢ pid[ e ] → vc[ send m e ] i ≡ vc[ e ] i
pid≢i⇒vc[send[e]]i≡vc[e]i e _ i i≢pid = updateAt-minimal i pid[ e ] vc[ e ] i≢pid

pid≢i⇒vc[init]i≡0 : ∀ {pid} i → i ≢ pid → vc[ init {pid} ] i ≡ 0
pid≢i⇒vc[init]i≡0 {pid} i i≢pid = updateAt-minimal i pid (replicate 0) i≢pid

0<vc[e]pid[e] : 0 < vc[ e ] pid[ e ]
0<vc[e]pid[e] {pid} e@{e = init}    = subst (0 <_) (sym vc[init]pid≡1) (s≤s z≤n)
0<vc[e]pid[e] {pid} {e = send x e}  = subst (0 <_) (sym (updateAt-updates pid vc[ e ])) (<-trans (0<vc[e]pid[e]{e = e}) (s≤s ≤-refl))
0<vc[e]pid[e] {pid} {e = recv e e′} = <-trans (<-transˡ (0<vc[e]pid[e] {e = e′}) (zip⊔-monotonicʳ vc[ e′ ] vc[ e ] pid)) (vc[e]pid⊔bv[e′]pid<vc[recv[e,e′]]pid e e′)

clock-⊏-preserving : e ⊏ e′ →  vc[ e ] ≺ vc[ e′ ]
clock-⊏-preserving {e = e} {e′ = send m e} processOrder₁ = lemma , pid[ e ] , vc[e]pid<vc[send[e]]pid e m
  where
   lemma : Pointwise _≤_ vc[ e ] vc[ send m e ]
   lemma i with i Fin.≟ pid[ e ]
   ... | yes x rewrite x  = <⇒≤ (vc[e]pid<vc[send[e]]pid e m)
   ... | no x rewrite pid≢i⇒vc[send[e]]i≡vc[e]i e m i x = ≤-refl 
clock-⊏-preserving {e = e} {e′ = recv e′ e} processOrder₂ = lemma , pid[ e ] , (vc[e′]pid<vc[recv[e,e′]]pid e′ e)
  where
   lemma : Pointwise _≤_ vc[ e ] vc[ recv e′ e ]
   lemma i with i Fin.≟ pid[ e ]
   ... | yes x rewrite x  = <⇒≤ (vc[e′]pid<vc[recv[e,e′]]pid e′ e ) 
   ... | no x = pid≢i⇒vc[e′]i≤vc[recv[e,e′]]i e′ e i x
clock-⊏-preserving {e = e} {e′ = recv e e′} send⊏recv = lemma , pid[ e′ ] , vc[e]pid<vc[recv[e,e′]]pid e e′ 
  where
   lemma : Pointwise _≤_ vc[ e ] vc[ recv e e′ ]
   lemma i with i Fin.≟ pid[ e′ ]
   ... | yes x rewrite x  = <⇒≤ (vc[e]pid<vc[recv[e,e′]]pid e e′)
   ... | no x = pid≢i⇒vc[e]i≤vc[recv[e,e′]]i e e′ i x
clock-⊏-preserving {e = e} {e′ = e′} (trans x x₁) = ≺-trans (clock-⊏-preserving x) (clock-⊏-preserving x₁)

-- other lemmas about vc[_]

⊏-preserving-index : e ⊏ e′ →  vc[ e ] pid[ e′ ] < vc[ e′ ] pid[ e′ ]
⊏-preserving-index {e = e} {e′ = send m e}  processOrder₁      = vc[e]pid<vc[send[e]]pid e m
⊏-preserving-index {e = e} {e′ = recv e′ e} processOrder₂      = vc[e′]pid<vc[recv[e,e′]]pid e′ e
⊏-preserving-index {e = e} {e′ = recv e e′} send⊏recv          = vc[e]pid<vc[recv[e,e′]]pid e e′
⊏-preserving-index (trans {_} {_} {_} {_} {_} {_} {pid″} x y)  = <-transʳ (proj₁ (clock-⊏-preserving x) pid″) (⊏-preserving-index y)

⊏-determining-index : pid[ e ] ≢ pid[ e′ ] → vc[ e ] pid[ e ] ≤ vc[ e′ ] pid[ e ] → e ⊏ e′
⊏-determining-index {e = e} e′@{e′ = init} x y = ⊥-elim (≤⇒≯ y (subst ( vc[ e ] pid[ e ] >_) z (0<vc[e]pid[e] {e = e})))
  where
   z : 0 ≡ vc[ e′ ] pid[ e ]
   z = sym (updateAt-minimal pid[ e ] pid[ e′ ] (replicate 0) x)
⊏-determining-index {e = e} {e′ = send m e′} x y = trans (⊏-determining-index x (subst (vc[ e ] pid[ e ] ≤_) z y)) processOrder₁
  where
   z : vc[ send m e′ ] pid[ e ] ≡ vc[ e′ ] pid[ e ]
   z = updateAt-minimal pid[ e ] pid[ e′ ] vc[ e′ ] x
⊏-determining-index {e = e} {e′ = recv e″ e′} x y
  with z ← subst ( vc[ e ] pid[ e ] ≤_ ) (sym (pid≢i⇒vc[e]⊔vc[e′]i≡vc[recv[e,e′]]i e″ e′ pid[ e ] x)) y -- vc[ e ] pid[ e ] ≤ vc[ e″ ] pid[ e ] ⊔ vc[ e′ ] pid[ e ]
  with vc[ e″ ] pid[ e ] ≤? vc[ e′ ] pid[ e ]
...| yes w
     with u ← subst ( vc[ e ] pid[ e ] ≤_ ) (m≤n⇒m⊔n≡n w) z -- vc[ e ] pid[ e ] ≤ vc[ e′ ] pid[ e ] 
     = trans (⊏-determining-index x u) processOrder₂
...| no w
     with u ← subst ( vc[ e ] pid[ e ] ≤_ ) (m≥n⇒m⊔n≡m (<⇒≤ (≰⇒> w))) z -- vc[ e ] pid[ e ] ≤ vc[ e″ ] pid[ e ]  
     with pid[ e ] Fin.≟ pid[ e″ ]
...   | no v = trans (⊏-determining-index v u) send⊏recv
...   | yes refl with ⊏-tri-locally {e = e} {e′ = e″} refl 
...            | inj₁ v           = trans v send⊏recv
...            | inj₂ (inj₁ refl) = send⊏recv
...            | inj₂ (inj₂ v)    = ⊥-elim (<⇒≱ (⊏-preserving-index v) u)

clock-⊏-determining : vc[ e ] ≺ vc[ e′ ] → e ⊏ e′
clock-⊏-determining {e = e} {e′ = e′} z@(∀≤ , pid , p<p) with pid[ e ] Fin.≟ pid[ e′ ]
... | no pid≢ = ⊏-determining-index pid≢ (∀≤ _)
... | yes pid≡ with ⊏-tri-locally {e = e} {e′ = e′} pid≡
...             | inj₁ x = x
...             | inj₂ (inj₁ refl) = ⊥-elim (1+n≰n p<p)
...             | inj₂ (inj₂ x) = ⊥-elim (≺-irrefl (≺-trans z (clock-⊏-preserving x)))

