module VectorClockFunctional where

open import Postulates
open import Event
open import Clock
open import Data.Fin as Fin using (Fin)
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; ∃-syntax; _,_)
open import Data.Vec.Functional as Vector
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as VectorEq
open import Data.Vec.Functional.Relation.Binary.Pointwise
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwiseₚ
open import Function using (const)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open VectorEq (DecSetoid.setoid ℕₚ.≡-decSetoid)

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

vc[_] : Event pid eid → VC
vc[_] {pid} init        = updateAt pid (const 1) (replicate 0)
vc[_] {pid} (send _ e)  = updateAt pid (1 +_) vc[ e ]
vc[_] {pid} (recv e e′) = updateAt pid (1 +_) (zipWith _⊔_ vc[ e ] vc[ e′ ])

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

clock : Clock
clock = {!!}

clock-⊏-preserving : ⊏-Preserving clock
clock-⊏-preserving = {!!}
