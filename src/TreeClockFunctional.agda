module TreeClockFunctional where

open import Postulates
open import Event
open import HappensBefore
open import VectorClockFunctional using (VC; vc[_]; _≺_; ≺-preserves-⊏; ≺-reflects-⊏)

open import Data.Bool using (true;false;if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as ℕ
open import Data.Nat.Properties as NatProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; ∃-syntax; _,_;proj₁;proj₂)
open import Data.Vec.Functional using (Vector; updateAt; zipWith; map; replicate)
open import Data.Vec.Functional.Properties using (updateAt-updates; updateAt-minimal)
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as VectorEq
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwiseₚ
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Function using (const)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality using (refl;_≅_;_≇_;≅-to-≡) renaming(cong to hetero-cong;subst to hetero-subst)
open import Relation.Binary.PropositionalEquality as Eq using (refl;_≡_;subst;sym;cong;cong-app;_≢_)
open import Relation.Nullary using (¬_;_because_;ofⁿ;ofʸ;yes;no;does)

open VectorEq (DecSetoid.setoid NatProp.≡-decSetoid) using (_≋_)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

record TCVal : Set where
  constructor p:_c:_a:_
  field
    prt : Maybe ProcessId
    clk : ℕ
    aclk : ℕ

open TCVal

updatePrt : (Maybe (Fin n) →  Maybe (Fin n)) → TCVal → TCVal
updatePrt f tc = record tc {prt = f (prt tc)}

updateClk : (ℕ → ℕ) → TCVal → TCVal
updateClk f tc = record tc {clk = f (clk tc)}

updateAClk : (ℕ → ℕ) → TCVal → TCVal
updateAClk f tc = record tc {aclk = f (aclk tc)}

TC : Set
TC = Vector TCVal n

TC-to-VC : TC → VC
TC-to-VC  tc = map clk tc

mergePrt : ProcessId → ProcessId → ProcessId → TCVal → TCVal → Maybe ProcessId
mergePrt pid′ pid curPid tc′ tc =
  if (does (pid Fin.≟ curPid))
  then nothing
  else (if (does (clk tc <? clk tc′))
        then (if (does (pid′ Fin.≟ curPid)) then (just pid) else prt tc′)
        else prt tc)

getNewAClk : ProcessId → ProcessId → ℕ → ℕ → ℕ
getNewAClk pid curPid clk aclk = if (does (pid Fin.≟ curPid)) then clk else aclk

mergeTCVal : ProcessId → ProcessId → ProcessId → TCVal →  TCVal → TCVal
mergeTCVal pid′ pid curPid tcv′ tcv =
  record
     { prt  = mergePrt pid′ pid curPid tcv′ tcv
     ; clk  = (_⊔_ (clk tcv′) (clk tcv))
     ; aclk = getNewAClk pid′ curPid (clk tcv) (aclk tcv′)
     }
                      
zipWith′ : ∀ {n}{A B C : Set} → (Fin n → A → B → C) → Vector A n → Vector B n → Vector C n
zipWith′ f xs ys i = f i (xs i) (ys i)

tc[_] : Event pid eid → TC
tc[_] {pid} init        = updateAt pid (updateClk suc) (replicate (p: nothing c: 0 a: 0))
tc[_] {pid} (send _ e)  = updateAt pid (updateClk suc) tc[ e ]
tc[_] {pid}(recv {_} {pid′} e′ e ) = updateAt pid (updateClk suc) (zipWith′ (mergeTCVal pid′ pid) tc[ e′ ] tc[ e ] )

TC-VC-Obs-Equiv : vc[ e ] ≋ TC-to-VC tc[ e ]
TC-VC-Obs-Equiv {pid} {e = init} i with i Fin.≟ pid
... | yes refl
  rewrite updateAt-updates i {f = suc} (replicate 0)
        | updateAt-updates i {f = updateClk suc} (replicate (p: nothing c: 0 a: 0))
  = refl
... | no neq
  rewrite updateAt-minimal i pid {f = suc}  (replicate 0) neq
        | updateAt-minimal i pid {f = updateClk suc} (replicate (p: nothing c: 0 a: 0)) neq
  = refl
TC-VC-Obs-Equiv {pid} {e = send _ e} i with i Fin.≟ pid
... | yes refl
  rewrite updateAt-updates i {f = suc} vc[ e ]
        | updateAt-updates i {f = updateClk suc} tc[ e ]
  = cong suc (TC-VC-Obs-Equiv {e = e} i)
... | no neq
  rewrite updateAt-minimal i pid {f = suc}  vc[ e ] neq
        | updateAt-minimal i pid {f = updateClk suc} tc[ e ] neq
  = TC-VC-Obs-Equiv {e = e} i
TC-VC-Obs-Equiv {pid} {e = recv {_} {pid′} e′ e} i with i Fin.≟ pid
... | yes refl
  rewrite updateAt-updates i {f = suc} (zipWith _⊔_ vc[ e′ ] vc[ e ])
        | updateAt-updates i {f = updateClk suc} (zipWith′ (mergeTCVal pid′ pid) tc[ e′ ] tc[ e ] )
        | TC-VC-Obs-Equiv {e = e} i
        | TC-VC-Obs-Equiv {e = e′} i
  = refl
... | no neq
  rewrite updateAt-minimal i pid {f = suc} (zipWith _⊔_ vc[ e′ ] vc[ e ]) neq
        | updateAt-minimal i pid {f = updateClk suc} (zipWith′ (mergeTCVal pid′ pid) tc[ e′ ] tc[ e ]) neq
        | TC-VC-Obs-Equiv {e = e} i
        | TC-VC-Obs-Equiv {e = e′} i
  = refl

_≺ᵗ_ : TC → TC → Set
tc ≺ᵗ tc′ = (TC-to-VC tc) ≺ (TC-to-VC tc′)

≺ᵗ⇒≺ : tc[ e ] ≺ᵗ tc[ e′ ] → vc[ e ] ≺ vc[ e′ ]
≺ᵗ⇒≺ {e = e} {e′ = e′} (H≤ , j , H<) =  H≤′ , (j , H<′)
  where
   H≤′ : (i : Fin n) → vc[ e ] i ≤ vc[ e′ ] i
   H≤′ i rewrite TC-VC-Obs-Equiv {e = e} i
             | TC-VC-Obs-Equiv {e = e′} i
       = H≤ i
   H<′ : vc[ e ] j < vc[ e′ ] j
   H<′ rewrite TC-VC-Obs-Equiv {e = e} j
            | TC-VC-Obs-Equiv {e = e′} j
      = H<
≺⇒≺ᵗ :  vc[ e ] ≺ vc[ e′ ] → tc[ e ] ≺ᵗ tc[ e′ ]
≺⇒≺ᵗ {e = e} {e′ = e′} (H≤ , j , H<) =  H≤′ , (j , H<′)
  where
   H≤′ : (i : Fin n) → clk (tc[ e ] i) ≤ clk (tc[ e′ ] i)
   H≤′ i rewrite sym (TC-VC-Obs-Equiv {e = e} i)
             | sym (TC-VC-Obs-Equiv {e = e′} i)
       = H≤ i
   H<′ : clk (tc[ e ] j) < clk (tc[ e′ ] j)
   H<′ rewrite sym (TC-VC-Obs-Equiv {e = e} j)
            | sym (TC-VC-Obs-Equiv {e = e′} j)
      = H<
      
≺ᵗ-preserves-⊏ : e ⊏ e′ → tc[ e ] ≺ᵗ tc[ e′ ]
≺ᵗ-preserves-⊏ {e = e} {e′ = e′} x = ≺⇒≺ᵗ {e = e} {e′ = e′} (≺-preserves-⊏ x)

≺ᵗ-reflects-⊏ : tc[ e ] ≺ᵗ tc[ e′ ] → e ⊏ e′
≺ᵗ-reflects-⊏ {e = e} {e′ = e′} x = ≺-reflects-⊏ (≺ᵗ⇒≺ {e = e} {e′ = e′} x)
