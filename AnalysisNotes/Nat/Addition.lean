/-
  Addition of Natural Numbers
  ===========================

  This file defines the addition operation for the natural numbers introduced in
  `Peano.lean`. It includes the core definition, basic notation, key theorems,
  and simplification lemmas for automated reasoning.
-/

import AnalysisNotes.Nat.Peano


namespace ℕ

-- Definitions & Notations
-- =======================

-- Addition between two natural numbers.
def add : ℕ → ℕ → ℕ
  | 0,  n => n
  | m⁺, n => (add m n)⁺

-- This instance allows using `+` with ℕ.
instance : Add ℕ where
  add := add

-- Basic check.
#eval 0⁺⁺ + 0⁺   -- ℕ.succ (ℕ.succ (ℕ.succ (ℕ.zero)))


-- Simplification Support for `simp` Tools
-- =======================================

-- These two lines allow `simp` to reduce types using addition of ℕ.
@[simp] theorem zero_add (n : ℕ) : 0 + n = n := rfl
@[simp] theorem succ_add (m n : ℕ) : m⁺ + n = (m + n)⁺ := rfl

-- Allows `simp` to recognize `1 + n` as equivalent to `n⁺`, which is convenient
-- in proofs involving inequalities or successor expressions.
@[simp]
theorem one_add_eq_succ : ∀ (n : ℕ), 1 + n = n⁺
  | _ => by rw [one_eq_succ_zero, succ_add, zero_add]


-- Addition Commutativity
-- ======================

-- The addition of natural numbers is commutative means `a + b = b + a`.
-- The proof procceds in three steps by nested induction on both arguments,
-- using lemmas we construct along the way.

-- First: we show the addition with zero is commutative.
@[simp]
theorem add_zero : ∀ (n : ℕ), n + 0 = n
  | 0  => rfl
  | m⁺ => by
    have ih := add_zero m  -- inductive hypothesis
    rw [succ_add, ih]

-- Second: we show that addition with the successor is commutative.
@[simp]
theorem add_succ (n : ℕ) : ∀ (m : ℕ), m + n⁺ = (m + n)⁺
  | 0  => by repeat rw [zero_add]
  | k⁺ => by
    have ih := add_succ n k  -- inductive hypothesis
    rw [succ_add, succ_add, ih]

-- Finally: we use the two lemmas above to prove that addition is commutative.
@[simp]
theorem add_comm (m: ℕ) : ∀ (n : ℕ), m + n = n + m
  | 0  => by rw [add_zero, zero_add]
  | k⁺ => by
    have ih := add_comm m k  -- inductive hypothesis
    rw [add_succ, succ_add, ih]


-- Addition Associativity
-- ======================

-- The associative property means multiple addition operations like `a + b + c`
-- can be executed in any order, `(a + b) + c = a + (b + c)`.
@[simp]
theorem add_assoc (a b : ℕ) : ∀ (c : ℕ), (a + b) + c = a + (b + c)
  | 0 => by repeat rw [add_zero]
  | k⁺ => by
    have ih := add_assoc a b k  -- inductive hypothesis
    rw [add_succ, ih, ← add_succ, ← add_succ]


-- Addition Cancellation
-- =====================

-- Enables simplification of equalities by eliminating common terms on both
-- sides of the equation.
--
-- In equalities involving addition, the common term can appear either on the
-- left or right side of the `+` operator.

-- Cancellation where the common term is on the left of the addition.
@[simp]
theorem add_cancel_left (a b c : ℕ) (h : a + b = a + c) : b = c :=
  match a with
  | 0 => by
    simp at h
    exact h
  | k⁺ => by
    have ih := add_cancel_left k b c  -- inductive hypothesis
    rw [succ_add, succ_add] at h
    apply ih
    apply Iff.mp (succ_inj (k+b) (k+c))
    exact h

-- Cancellation where the common term is on the right of the addition.
@[simp]
theorem add_cancel_right (a b c : ℕ) (h : a + c = b + c) : a = b := by
  rw [add_comm a c, add_comm b c] at h
  apply add_cancel_left c a b h

end ℕ
