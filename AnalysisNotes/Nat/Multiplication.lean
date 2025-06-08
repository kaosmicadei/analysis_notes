import AnalysisNotes.Nat.Peano
import AnalysisNotes.Nat.Addition

namespace ℕ

-- Recursive definition of the multiplicatoin between two natural numbers.
def mul : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m⁺, n => n + (mul m n)

-- Allows to use the multiplication operator with ℕ.
instance : Mul ℕ where
  mul := mul

#eval 0⁺⁺ * 0⁺⁺  -- ℕ.succ (ℕ.succ (ℕ.succ (ℕ.succ (ℕ.zero))))

@[simp] theorem zero_mul (n : ℕ) : 0 * n = 0 := rfl
@[simp] theorem succ_mul (m n : ℕ) : m⁺ * n = n + (m * n) := rfl

@[simp]
theorem mul_zero : ∀ (n : ℕ), n * 0 = 0
  | 0  => rfl
  | k⁺ => by
    rw [succ_mul]
    rw [mul_zero k]  -- by hypotesis
    rw [add_zero]

@[simp]
theorem mul_one : ∀ (n : ℕ), n * 1 = n
  | 0  => by rw [zero_mul]
  | k⁺ => by
    rw [succ_mul, one_add_eq_succ]
    rw [mul_one]  -- hypotesis

@[simp]
theorem one_mul : ∀ (n : ℕ), 1 * n = n
  | 0  => by rw [mul_zero]
  | k⁺ => by rw [one_eq_succ_zero, succ_mul, zero_mul, add_zero]

@[simp]
theorem mul_succ (n : ℕ) : ∀ (m : ℕ), m * n⁺ = m + (m * n)
  | 0 => by
    rw [zero_mul, zero_mul, add_zero]
  | k⁺ => by
    rw [succ_mul, succ_mul, succ_add, succ_add]
    rw [mul_succ]
    rw [add_comm, add_assoc, add_comm (k * n)]

-- Proof that multiplication is commutative: a * b = b * a
@[simp]
theorem mul_comm (a : ℕ) : ∀ (b : ℕ), a * b = b * a
  | 0 => by rw [mul_zero, zero_mul]
  | k⁺ => by
    rw [mul_succ, succ_mul]
    rw [mul_comm] -- hypotesis

end ℕ


-- Proofs involving addition and multiplication of natural numbers.
namespace ℕ

@[simp]
theorem mul_add (b c : ℕ) : ∀ (a : ℕ), a * (b + c) = a * b + a * c
  | 0  => by
    repeat rw [zero_mul]
    rw [add_zero]
  | k⁺ => by
    rw [succ_mul, succ_mul, succ_mul]
    rw [mul_add] -- hypotesis
    rw [add_comm (k * b), ← add_assoc, add_comm, ← add_assoc, ← add_assoc]
    rw [add_comm (k * b), ← add_assoc]

@[simp]
theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

-- Proof that multiplication is associative: (a * b) * c = a * (b * c)
@[simp]
theorem mul_assoc (a b: ℕ) : ∀ (c : ℕ), (a * b) * c = a * (b * c)
  | 0 => by repeat rw [mul_zero]
  | k⁺ => by
    rw [mul_succ, mul_succ, mul_add]
    rw [mul_assoc] -- hypotesis

end ℕ
