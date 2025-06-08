import AnalysisNotes.Nat.Peano


namespace ℕ

-- Recursive definition of the addition between two natural numbers.
def add : ℕ → ℕ → ℕ
  | 0,  n => n
  | m⁺, n => (add m n)⁺

-- Allows to use the addition operator with ℕ.
instance : Add ℕ where
  add := add

#eval 0⁺⁺ + 0⁺   -- ℕ.succ (ℕ.succ (ℕ.succ (ℕ.zero)))

@[simp] theorem zero_add (n : ℕ) : 0 + n = n := rfl
@[simp] theorem succ_add (m n : ℕ) : m⁺ + n = (m + n)⁺ := rfl

@[simp]
theorem add_zero : ∀ (n : ℕ), n + 0 = n
  | 0  => rfl
  | m⁺ => by
    rw [succ_add]
    rw [add_zero m]  -- here we use the theorem hypotesis

@[simp]
theorem add_succ (n : ℕ) : ∀ (m : ℕ), m + n⁺ = (m + n)⁺
  | 0  => by repeat rw [zero_add]
  | k⁺ => by
    repeat rw [succ_add]
    rw [add_succ]  -- use of the hypotesis

@[simp]
theorem add_one_eq_succ : ∀ (n : ℕ), n + 1 = n⁺
  | 0  => by rw [zero_add]; rfl
  | k⁺ => by rw [succ_add, one_eq_succ_zero, add_succ, add_zero]

@[simp]
theorem one_add_eq_succ : ∀ (n : ℕ), 1 + n = n⁺
  | 0  => by rw [add_zero]; rfl
  | k⁺ => by rw [one_eq_succ_zero, succ_add, zero_add]

-- Proof that addition is commutative: m + n = n + m
@[simp]
theorem add_comm (m: ℕ) : ∀ (n : ℕ), m + n = n + m
  | 0  => by rw [add_zero, zero_add]
  | k⁺ => by rw [add_succ, succ_add, add_comm]
                                     -- ^ hypotesis

-- Proof that addition is associative: (a + b) + c = a + (b + c)
@[simp]
theorem add_assoc (a b : ℕ) : ∀ (c : ℕ), (a + b) + c = a + (b + c)
  | 0 => by repeat rw [add_zero]
  | k⁺ => by
    rw [add_succ]
    rw [add_assoc]
    repeat rw [← add_succ]

@[simp]
theorem add_cancel_left (a b c : ℕ) (h : a + b = a + c) : b = c :=
  match a with
  | 0 => by
    simp at h
    exact h
  | k⁺ => by
    rw [succ_add, succ_add] at h
    apply add_cancel_left k b c  -- inductive hypotesis
    apply Iff.mp (succ_inj (k+b) (k+c))
    exact h

@[simp]
theorem add_cancel_right (a b c : ℕ) (h : a + c = b + c) : a = b := by
  rw [add_comm a c, add_comm b c] at h
  apply add_cancel_left c a b h

end ℕ
