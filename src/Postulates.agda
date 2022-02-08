------------------------------------------------------------------------
-- Global postulates used across the whole project.
------------------------------------------------------------------------

module Postulates where

open import Data.Nat using (ℕ)

postulate
  -- the number of processes
  n : ℕ
  -- the type of messages sent and received by each process
  Message : Set
