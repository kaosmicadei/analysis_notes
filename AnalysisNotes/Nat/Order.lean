import AnalysisNotes.Nat.Peano
import AnalysisNotes.Nat.Addition
import AnalysisNotes.Nat.Multiplication


-- Partial Order
-- =============

namespace ℕ

def le (m n : ℕ) : Prop := ∃ k, m + k = n

notation m " ≤ " n => le m n

@[simp]
theorem zero_le (n : ℕ) : 0 ≤ n  -- := ⟨n, by simp⟩
  := by
  unfold le
  apply Exists.intro n
  rw [zero_add]

@[simp]
theorem le_refl (n : ℕ) : n ≤ n := by
  unfold le
  apply Exists.intro 0
  rw [add_zero]

@[simp]
theorem le_trans (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  unfold le at h₁ h₂
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  rw [← hk₁] at hk₂
  unfold le
  apply Exists.intro (k₁ + k₂)
  rw [← add_assoc]
  exact hk₂

theorem le_antisymm (a b : ℕ) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  rw [← hk₁] at hk₂
  have h : k₁ + k₂ = 0 := by
    apply add_cancel_left a
    rw [← add_assoc, add_zero]
    exact hk₂
  have k_zero : k₁ = 0 := And.left (add_eq_zero k₁ k₂ h)
  rw [k_zero, add_zero] at hk₁
  exact hk₁

@[simp]
theorem le_self_succ (n : ℕ) : n ≤ n⁺ := by
  unfold le
  apply Exists.intro 1
  rw [add_comm, one_add_eq_succ]

@[simp]
theorem le_succ (m n : ℕ) (h : m ≤ n) : m ≤ n⁺ := by
  unfold le at h
  obtain ⟨k, hk⟩ := h
  unfold le
  apply Exists.intro (k⁺)
  rw [add_succ, hk]

@[simp]
theorem succ_le_succ (m n : ℕ) (h : m ≤ n) : m⁺ ≤ n⁺ := by
  unfold le at h
  obtain ⟨k, hk⟩ := h
  unfold le
  apply Exists.intro k
  rw [succ_add, hk]

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



theorem mul_le_mul (a b c : ℕ) (h : a ≤ b) : (a * c) ≤ (b * c) :=
  match c with
  | 0 => by
    repeat rw [mul_zero]
    exact le_refl 0
  | k⁺ => by
    repeat rw [mul_succ]
    have h₁ : (a * k) ≤ (b * k) := mul_le_mul a b k h
    have h₂ := add_le_add (a * k) (b * k) a h₁
    have h₃ := add_le_add a b (b * k) h
    rw [add_comm, add_comm (b * k) a] at h₂
    exact le_trans _ _ _ h₂ h₃ -- let the compiler infer a, b and c

@[simp]
theorem le_add_le (a b c d : ℕ) (h₁ : a ≤ b) (h₂ : c ≤ d) : (a + c) ≤ (b + d)
  := by
  have l₁ := add_le_add a b c h₁
  have l₂ := add_le_add c d b h₂
  rw [add_comm, add_comm d b] at l₂
  exact le_trans _ _ _ l₁ l₂

@[simp]
theorem le_mul_right (a b c : ℕ) (h : a ≤ b) : (a * c) ≤ (b * c)
  := mul_le_mul a b c h

@[simp]
theorem le_mul_left (a b c : ℕ) (h : a ≤ b) : (c * a) ≤ (c * b)
  := by
  rw [mul_comm, mul_comm c]
  exact mul_le_mul a b c h

end ℕ


-- Strict Partial Order
-- ====================

namespace ℕ

def lt (m n : ℕ) : Prop := ∃ k, m + k⁺ = n

notation m " < " n => lt m n

theorem lt_irrefl (a : ℕ) : (a < a) → False
  := λ ⟨k, hk⟩ => by
  have h : k⁺ = 0 := by
    apply add_cancel_left a
    rw [add_zero]
    exact hk
  nomatch h

theorem lt_trans (a b c : ℕ) (h₁ : a < b) (h₂ : b < c) : a < c := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  rw [← hk₁] at hk₂
  unfold lt
  apply Exists.intro (k₁ + k₂⁺)
  rw [← succ_add, ← add_assoc]
  exact hk₂

end ℕ
