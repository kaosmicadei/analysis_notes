import  AnalysisNotes.Integer.Int


namespace ℤ

@[simp] def add' : ℤ₀ → ℤ₀ → ℤ := λ (a, b) (c, d) => mk (a + c, b + d)

theorem add_well_defined (a b c d : ℤ₀) (h₁ : a ≈ c) (h₂ : b ≈ d) :
  add' a b = add' c d
  := by
  apply Quotient.sound
  simp [· ≈ ·, Setoid.r] at *
  -- LHS
  rw [← ℕ.add_assoc b.1, ℕ.add_comm b.1, ℕ.add_assoc c.2, ← ℕ.add_assoc a.1, h₁, h₂, ← ℕ.add_assoc]
  -- RHS
  rw [← ℕ.add_assoc d.1, ← ℕ.add_assoc, ℕ.add_comm d.1, ← ℕ.add_assoc]

@[simp] def add : ℤ → ℤ → ℤ := Quotient.lift₂ add' add_well_defined

instance : Add ℤ where
  add := add

#check (1 : ℤ) + 1
#check (1 : ℤ) + (-1)

instance : Sub ℤ where
  sub := λ a b => a + (-b)

#check (1 : ℤ) - 1

@[simp]
theorem add_inv_eq_zero (n : ℤ) : n + (-n) = 0 := by
  cases n using Quotient.ind
  apply Quotient.sound
  simp [· ≈ ·, Setoid.r, ℕ.zero_eq_nat_zero]

@[simp]
theorem sub_eq_add_inv (a b : ℤ) : a - b = a + (-b) := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  apply Quotient.sound
  simp [· ≈ ·, Setoid.r]

@[simp]
theorem add_zero (n : ℤ) : n + 0 = n := by
  cases n using Quotient.ind
  apply Quotient.sound
  simp [· ≈ ·, Setoid.r, ℕ.zero_eq_nat_zero]

@[simp]
theorem zero_add (n : ℤ) : 0 + n = n := by
  cases n using Quotient.ind
  apply Quotient.sound
  simp [· ≈ ·, Setoid.r, ℕ.zero_eq_nat_zero]

@[simp]
theorem add_comm (a b : ℤ) : a + b = b + a := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  apply Quotient.sound
  simp [· ≈ ·, Setoid.r]

@[simp]
theorem add_assoc (a b c : ℤ) : (a + b) + c = a + (b + c) := by
  cases a using Quotient.ind
  cases b using Quotient.ind
  cases c using Quotient.ind
  rename_i a b c  -- make inaccessible variables accessible
  apply Quotient.sound
  simp [· ≈ ·, Setoid.r]
  repeat rw [← ℕ.add_assoc]
  rw [ℕ.add_assoc c.1, ℕ.add_comm c.1]
  rw [ℕ.add_assoc, ℕ.add_assoc, ← ℕ.add_assoc a.2, ℕ.add_comm _ c.2]
  repeat rw [← ℕ.add_assoc]

example (a b c d : ℤ) (h : a + c = b + d) : a - b = d - c := by
  simp
  rw [← add_zero a, ← add_inv_eq_zero c, ← add_assoc, h]
  simp
  rw [← add_assoc]
  simp


end ℤ
