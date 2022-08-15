module TreeClockFunctional where

open import Postulates
open import Event
open import HappensBefore
open import VectorClockFunctional using (VC)

open import Data.Bool using (true;false;if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as ℕ
open import Data.Nat.Properties as NatProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; ∃-syntax; _,_;proj₁;proj₂)
open import Data.Vec.Functional using (Vector; updateAt; map; replicate)
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as VectorEq
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwiseₚ
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Function using (const)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality using (refl;_≅_;_≇_;≅-to-≡) renaming(cong to hetero-cong;subst to hetero-subst)
open import Relation.Binary.PropositionalEquality as Eq using (refl;_≡_;subst;sym;cong;cong-app;_≢_)
open import Relation.Nullary using (¬_;_because_;ofⁿ;ofʸ;yes;no;does)

open VectorEq (DecSetoid.setoid  NatProp.≡-decSetoid)

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
mergePrt pid pid′ curPid tc tc′ =
  if (does (pid′ Fin.≟ curPid))
  then nothing
  else (if (does (clk tc′ <? clk tc))
        then if (does (pid Fin.≟ curPid)) then (just pid′) else prt tc
        else prt tc′)

getNewAClk : ProcessId → ProcessId → ℕ → ℕ → ℕ
getNewAClk pid curPid clk aclk = if (does (pid Fin.≟ curPid)) then clk else aclk

mergeTCVal : ProcessId → ProcessId → ProcessId → TCVal →  TCVal → TCVal
mergeTCVal pid pid′ curPid tcv tcv′ = record
                      { prt  = mergePrt pid pid′ curPid tcv tcv′
                      ; clk  = (_⊔_ (clk tcv) (clk tcv′))
                      ; aclk = getNewAClk pid curPid (clk tcv) (aclk tcv′)
                      }
                      
zipWith′ : ∀ {n}{A B C : Set} → (Fin n → A → B → C) → Vector A n → Vector B n → Vector C n
zipWith′ f xs ys i = f i (xs i) (ys i)

-- TODO: switch e and e′

tc[_] : Event pid eid → TC
tc[_] {pid} init        = updateAt pid (updateClk suc) (replicate (p: nothing c: 0 a: 0))
tc[_] {pid} (send _ e)  = updateAt pid (updateClk suc) tc[ e ]
tc[_] {pid′}(recv {_} {pid} e e′ ) = updateAt pid′ (updateClk suc) (zipWith′ (mergeTCVal pid pid′) tc[ e ] tc[ e′ ] )
