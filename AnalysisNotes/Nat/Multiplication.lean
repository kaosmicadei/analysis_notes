/-
  Multiplication of Natural Numbers
  =================================

  This file defines multiplication operation for the natural numbers introduced
  in `Peano.lean`. It includes the core definition, basic notation, prove its
  fundamental properties such as associativity, commutativity, and
  distributivity.
-/

import AnalysisNotes.Nat.Peano
import AnalysisNotes.Nat.Addition

namespace ℕ

-- Definitions & Notations
-- =======================

-- Multiplication between two natural numbers.
def mul : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m⁺, n => n + (mul m n)

-- This instance allows using `+` with ℕ.
instance : Mul ℕ where
  mul := mul

-- Quick evaluation to test definition.
#eval 1⁺ * 1⁺  -- ℕ.succ (ℕ.succ (ℕ.succ (ℕ.succ (ℕ.zero))))


-- Simplification Support for `simp` Tools
-- =======================================

-- These next two theorems lines allow `simp` to simplify expressions involving
-- multiplication.
@[simp] theorem zero_mul (n : ℕ) : 0 * n = 0 := rfl
@[simp] theorem succ_mul (m n : ℕ) : m⁺ * n = n + (m * n) := rfl

-- Allows `simp` to recognize `1` as the identity for multiplication.
@[simp]
theorem one_mul (n : ℕ) : 1 * n = n
  := by rw [one_eq_succ_zero, succ_mul, zero_mul, add_zero]


-- Multiplication Commutativity
-- ============================

-- Multiplication of natural numbers is commutative: `a * b = b * a`.
-- The proof procceds in three steps by nested induction on both arguments,
-- using lemmas we construct along the way.

-- First: we show the multiplication with zero is commutative.
@[simp]
theorem mul_zero : ∀ (n : ℕ), n * 0 = 0
  | 0  => rfl
  | k⁺ => by
    have ih := mul_zero k  -- inductive hypothesis
    rw [succ_mul, ih, add_zero]

-- Second: we show that multiplication with the successor is commutative.
@[simp]
theorem mul_succ (n : ℕ) : ∀ (m : ℕ), m * n⁺ = m + (m * n)
  | 0 => by
    rw [zero_mul, zero_mul, add_zero]
  | k⁺ => by
    have ih := mul_succ n k  -- inductive hypothesis
    rw [succ_mul, succ_mul, succ_add, succ_add, ih]
    rw [add_comm, add_assoc, add_comm (k * n)]

-- Finally: using the two lemmas above, we prove that multiplication is
-- commutative for all natural numbers by induction on the second argument.
@[simp]
theorem mul_comm (a : ℕ) : ∀ (b : ℕ), a * b = b * a
  | 0 => by rw [mul_zero, zero_mul]
  | k⁺ => by
    have ih := mul_comm a k   -- inductive hypothesis
    rw [mul_succ, succ_mul, ih]


-- Distributive Property
-- =====================

-- The distributive property allows expanding a product over a sum, rewriting
-- `a * (b + c)` as `a * b + a * c`. This also supports factoring in the reverse
-- direction.

-- Multiplication can be distributed from the left.
@[simp]
theorem mul_add (b c : ℕ) : ∀ (a : ℕ), a * (b + c) = a * b + a * c
  | 0  => by
    repeat rw [zero_mul]
    rw [add_zero]
  | k⁺ => by
    have ih := mul_add b c k  -- inductive hypothesis
    rw [succ_mul, succ_mul, succ_mul, ih]
    rw [add_comm (k * b), ← add_assoc, add_comm, ← add_assoc, ← add_assoc]
    rw [add_comm (k * b), ← add_assoc]

-- Multiplication can be distributed from the right.
@[simp]
theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c
  := by rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]


-- Multiplication Associativity
-- ============================

-- The associative property allows multiplication to be regrouped:
-- `(a * b) * c = a * (b * c)`.

@[simp]
theorem mul_assoc (a b: ℕ) : ∀ (c : ℕ), (a * b) * c = a * (b * c)
  | 0 => by repeat rw [mul_zero]
  | k⁺ => by
    have ih := mul_assoc a b k  -- induction hypothesis
    rw [mul_succ, mul_succ, mul_add, ih]

end ℕ
