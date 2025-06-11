import AnalysisNotes.Natural


structure ℤ where
  mk :: (a b : ℕ)
  deriving Repr


namespace ℤ

instance : Zero ℤ where
  zero := ⟨0, 0⟩

instance : One ℤ where
  one := ⟨1, 0⟩

@[simp] def neg : ℤ → ℤ := λ ⟨a, b⟩ => ⟨b, a⟩

notation "⁻" x => neg x

#check ⁻1
#eval ⁻1

@[simp] theorem zero_eq_neg_zero : (0 : ℤ) = ⁻0 := rfl


@[simp] def eq : ℤ → ℤ → Prop := λ ⟨a, b⟩ ⟨c, d⟩ => a + d = b + c

notation x " ∼ " y => eq x y

@[simp] theorem eq_refl (x : ℤ) : x ∼ x := by simp
@[simp] theorem eq_symm (x y : ℤ) (h : x ∼ y) : y ∼ x := by simp at *; rw [h]
@[simp] theorem eq_trans (x y z : ℤ) (h₁ : x ∼ y) (h₂ : y ∼ z) : x ∼ z := by
  simp at *
  have h : x.a + y.b + z.b = y.a + x.b + z.b := by rw [h₁]
  rw [ℕ.add_assoc y.a, ℕ.add_comm x.b, ← ℕ.add_assoc, h₂] at h
  rw [ℕ.add_comm x.a, ℕ.add_comm z.a, ℕ.add_assoc y.b, ℕ.add_assoc y.b] at h
  apply ℕ.add_cancel_left y.b
  exact h

@[simp] def add : ℤ → ℤ → ℤ := λ ⟨a, b⟩ ⟨c, d⟩ => ⟨a + c, b + d⟩

instance : Add ℤ where
  add := add

#check (1 : ℤ) + 1
#eval (1 : ℤ) + 1


theorem add_inv (x : ℤ) : (x + ⁻x) ∼ 0 := by simp


@[simp] def sub : ℤ → ℤ → ℤ := λ a b => a + ⁻b

instance : Sub ℤ where
  sub := sub

#eval (1 : ℤ) - 1 

end ℤ
