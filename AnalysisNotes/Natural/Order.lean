/-
  Order of Natural Numbers
  ========================

  This files defines the partial and strict order for nthe natural numbers
  introduced in `Peano.lean`. It includes the core definition, basic notation,
  and proves fundamental relations of transivity, symmetry, and inequality
  relations involving addition and multiplication.
-/

import AnalysisNotes.Natural.Peano
import AnalysisNotes.Natural.Addition
import AnalysisNotes.Natural.Multiplication


-- Partial Order
-- =============

namespace ℕ

-- Definitions & Notations
-- =======================

-- Partial order between natural numbers.
-- --------------------------------------
--
-- Although an inductive definition like
--
--     inductive LTE : ℕ -> ℕ -> Prop where
--       | LTEZero {n : ℕ} : LTE 0 n
--       | LTESucc {m n : ℕ} : LTE m n -> LTE m.succ n.succ
--
-- would be great for type proofs, for pratical purposes, the classical
-- definition operational definition is more practical for "numerical" proofs.
-- So, for now, this file will cover only the operational definition

-- Operational definition of partial order.
def le (m n : ℕ) : Prop := ∃ k, m + k = n

-- Making `m ≤ n` as a shortcut for `le m n` makes type notations easier to read.
notation m " ≤ " n => le m n

-- Zero: The Smallest Natural
-- ==========================
--
-- Since the definition of `le` uses `Exists` structure and addition, we could
-- opt to use the struct constructor and the automatic simplitication rules
-- written in `Addition.lean` to construct the prove. But, because of the
-- pedagogical goal of this collection, we proceed with a more manual/laborous
-- demonstration in order to identify all the steps of the proof.
@[simp]
theorem zero_le (n : ℕ) : 0 ≤ n  -- := ⟨n, by simp⟩
  := by
  unfold le
  -- ^ Expands the definition of the function `le` exposing the quantified
  -- variable, ∃ k, 0 + k = n.

  apply Exists.intro n
  -- ^ Replace the quantified variable with the introduced value.
  -- ∃ k, 0 + k = n -> 0 + n = n.

  rw [zero_add]
  -- ^ Addition reduction.


-- Partial Order Relations
-- =========================
--
-- To be called "partially ordered", the inequality needs to hold three
-- properties:
-- 1. Reflexivity, n ≤ n.
-- 2. Antisymmetry, m ≤ n ∧ n ≤ m → m = n.
-- 3. Transitivity, a ≤ b ∧ b ≤ c → a ≤ c.

-- Relfexivity
-- -----------
--
-- From the definition, n ≤ n = ∃k, n + k = n. The trivial solution is k=0.
-- As before, we will prove this theorem step by step instead of using the
-- `Exists` constructor.
@[simp]
theorem le_refl (n : ℕ) : n ≤ n := by  -- := ⟨0, by simp⟩
  unfold le
  -- ^ Expands to ∃k, n + k = n.

  apply Exists.intro 0
  -- ^ Replaces k turning ∃k, n + k = n into n + 0 = n

  rw [add_zero]
  -- ^ Addition reduction.

-- Antisymmetry
-- ------------
--
-- To prove the antisymmetry property we start from two hypotesis: `a ≤ b` and
-- `b ≤ a`. The first unfolds as `∃k₁, a + k₁ = b` while the second expands to
-- `∃k₂, b + k₂ = a`.
--
-- The proof requires to use the first hypotesis on the second (or vice-versa)
-- and then prove that `k₁+k₂=0`. `Exists.intro` can only construct existential
-- proofs. To deconstruct we nee to use `cases h with` or `obtain ⟨_⟩ := h`
--
-- To deconstruct a single variable, both work fine. For more variables, it's
-- deconstruct them using `obtain` since `cases` would lead to less readable
-- nested cases.
theorem le_antisymm {a b : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  obtain ⟨k₁, hk₁⟩ := h₁
  -- ^ Similar to Exists.intro k₁ hk₁ = h₁ in Ocaml/Haskell.

  obtain ⟨k₂, hk₂⟩ := h₂
  -- ^ Exists.intro k₂ hk₂ = h₂.

  rw [← hk₁] at hk₂
  -- ^ Merging hypotesis.

  -- The key element here is to prove that k₁+k₂=0.
  have sum_is_zero : k₁ + k₂ = 0 := by
    apply add_cancel_left a
    rw [← add_assoc, add_zero]
    exact hk₂

  -- Over naturals, the only way a sum is zero is if each summand is zero.
  obtain ⟨k₁_is_zero, k₂_is_zero⟩ := add_eq_zero.mp sum_is_zero

  rw [k₁_is_zero, add_zero] at hk₁
  -- ^ Addition reduction.

  exact hk₁  -- QED


-- Transitivity
-- ------------
--
-- In simple terms, `a ≤ b ∧ b ≤ c → a ≤ c` means, `∃k₁, a + k₁ = b` and
-- `∃k₂, b + k₂ = c` that leads to `∃k₁ k₂, a + k₁ + k₂ = c`.
--
-- Here will need to combine construction and destruction of `Exists` type. We
-- use destruction to access the quantified variables and the construction to
-- construct the final proof.
@[simp]
theorem le_trans {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  obtain ⟨k₁, hk₁⟩ := h₁
  -- ^ Exists.intro k₁ hk₁ = h₁.

  obtain ⟨k₂, hk₂⟩ := h₂
  -- ^ Exists.intro k₂ hk₂ = h₂.

  rw [← hk₁] at hk₂
  -- ^ Merge hypotesis.

  unfold le
  -- ^ Hypotesis, ∃k, a + k = c.

  apply Exists.intro (k₁ + k₂)
  -- ^ Replace k=k₁+k₂

  rw [← add_assoc]
  -- ^ Addition reduction.

  exact hk₂  -- QED


-- Inequalities With Sucessor
-- ==========================

-- To prove inequalities involving addition, first we need proofs relative to
-- the successor. This is done in the following proofs.

@[simp]
theorem le_self_succ (n : ℕ) : n ≤ n⁺ := by
  unfold le
  apply Exists.intro 1
  rw [add_comm, one_add_eq_succ]

@[simp]
theorem le_succ (m n : ℕ) (h : m ≤ n) : m ≤ n⁺ := by
  obtain ⟨k, hk⟩ := h
  unfold le
  apply Exists.intro (k⁺)
  rw [add_succ, hk]

@[simp]
theorem succ_le_succ (m n : ℕ) (h : m ≤ n) : m⁺ ≤ n⁺ := by
  obtain ⟨k, hk⟩ := h
  unfold le
  apply Exists.intro k
  rw [succ_add, hk]


-- Addition Inequalities
-- =====================

@[simp]
theorem add_le_add (a b c : ℕ) (h : a ≤ b) : (a + c) ≤ (b + c) :=
  match c with
  | 0 => by
    repeat rw [add_zero]
    exact h
  | k⁺ => by
    repeat rw [add_succ]
    apply succ_le_succ
    exact add_le_add a b k h


-- Multiplication Inequalities
-- ===========================

@[simp]
theorem mul_le_mul_right (a b c : ℕ) (h : a ≤ b) : (a * c) ≤ (b * c) :=
  match c with
  | 0 => by
    repeat rw [mul_zero]
    exact le_refl 0
  | k⁺ => by
    repeat rw [mul_succ]
    have h₁ : (a * k) ≤ (b * k) := mul_le_mul_right a b k h
    have h₂ := add_le_add (a * k) (b * k) a h₁
    have h₃ := add_le_add a b (b * k) h
    rw [add_comm, add_comm (b * k) a] at h₂
    exact le_trans h₂ h₃

@[simp]
theorem mul_le_mul_left (a b c : ℕ) (h : a ≤ b) : (c * a) ≤ (c * b)
  := by
  rw [mul_comm c, mul_comm c]
  exact mul_le_mul_right a b c h


-- Algebraic Properties of Inequalities
-- ====================================

-- Addition between two inequalities.
@[simp]
theorem le_add_le (a b c d : ℕ) (h₁ : a ≤ b) (h₂ : c ≤ d) : (a + c) ≤ (b + d)
  := by
  have l₁ := add_le_add a b c h₁
  have l₂ := add_le_add c d b h₂
  rw [add_comm, add_comm d b] at l₂
  exact le_trans l₁ l₂

end ℕ


-- Strict Partial Order
-- ====================

namespace ℕ

-- Definitions & Notations
-- =======================

def lt (m n : ℕ) : Prop := ∃ k, m + k⁺ = n

notation m " < " n => lt m n

-- Strict Partial Order Is *Not* Reflexive
-- =======================================

theorem lt_irrefl (a : ℕ) : (a < a) → False
  := λ ⟨k, hk⟩ => by
  have h : k⁺ = 0 := by
    apply add_cancel_left a
    rw [add_zero]
    exact hk
  nomatch h


-- Strict Partial Order Transitivity
-- =================================

theorem lt_trans {a b c : ℕ} (h₁ : a < b) (h₂ : b < c) : a < c := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  rw [← hk₁] at hk₂
  unfold lt
  apply Exists.intro (k₁ + k₂⁺)
  rw [← succ_add, ← add_assoc]
  exact hk₂

end ℕ
