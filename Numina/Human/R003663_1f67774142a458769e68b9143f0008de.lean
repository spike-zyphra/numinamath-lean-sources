import Mathlib

open Polynomial

theorem algebra_205300 :
    {(x, y, z) : ℝ × ℝ × ℝ | x + 2 * y + 4 * z = 12 ∧ x * y + 4 * y * z + 2 * x * z = 22 ∧ x * y * z = 6}.ncard = 6 := by
  set S := {(x, y, z) : ℝ × ℝ × ℝ | x + 2 * y + 4 * z = 12 ∧ x * y + 4 * y * z + 2 * x * z = 22 ∧ x * y * z = 6} with hS
  set f : ℝ × ℝ × ℝ → List ℝ := fun (x, y, z) => [x / 2, y, 2 * z] with hf
  have hfinj : Function.Injective f := by
    intro ⟨x₁, y₁, z₁⟩ ⟨x₂, y₂, z₂⟩ h
    simp [hf, div_left_inj'] at h
    simp [h]
  have H := Set.ncard_image_of_injective (f := f) S hfinj
  have hfim : f '' S = {p | p ∈ List.permutations [1, 2, 3]} := by
    ext p
    constructor
    . simp [hf, hS]
      rintro a b c h₁ h₂ h₃ rfl
      have hP : (X - C (a / 2)) * (X - C b) * (X - C (2 * c)) = (X - C 1) * (X - C 2) * (X - C 3) := by
        calc (X - C (a / 2)) * (X - C b) * (X - C (2 * c))
          _ = X ^ 3 - (C (a / 2) + C b + C (2 * c)) * X ^ 2 + (C (a / 2) * C b + C (a / 2) * C (2 * c) + C b * C (2 * c)) * X - C (a / 2) * C b * C (2 * c) := by ring
          _ = X ^ 3 - (C (a / 2 + b + (2 * c))) * X ^ 2 + (C (a / 2 * b + a / 2 * (2 * c) + b * (2 * c))) * X - C ((a / 2) * b * (2 * c)) := by simp
          _ = X ^ 3 - C 6 * X ^ 2 + C 11 * X - C 6 := by congr <;> linarith
          _ = X ^ 3 - 6 * X ^ 2 + 11 * X - 6 := rfl
          _ = (X - 1) * (X - 2) * (X - 3) := by ring
      apply_fun (fun p => p.roots) at hP
      repeat rw [Polynomial.roots_mul (by simp [sub_eq_zero, Polynomial.X_ne_C, -map_mul, -map_one])] at hP
      simp [Polynomial.roots_X_sub_C, -map_mul, -map_one] at hP
      exact Multiset.coe_eq_coe.mp hP
    . have hperm : ([1, 2, 3] : List ℝ).permutations = [[1, 2, 3], [2, 1, 3], [3, 2, 1], [2, 3, 1], [3, 1, 2], [1, 3, 2]] := by simp [List.permutations, List.permutationsAux.rec]
      simp [hperm, hf, hS]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      . use 2, 2, 3 / 2
        norm_num
      . use 4, 1, 3 / 2
        norm_num
      . use 6, 2, 1 / 2
        norm_num
      . use 4, 3, 1 / 2
        norm_num
      . use 6, 1, 1
        norm_num
      . use 2, 3, 1
        norm_num
  rw [← H, hfim]
  have h : {p | p ∈ ([1, 2, 3] : List ℝ).permutations} = ([1, 2, 3] : List ℝ).permutations.toFinset := by simp
  rw [h, Set.ncard_coe_Finset, List.toFinset_card_of_nodup (List.nodup_permutations _ (by simp)), List.length_permutations]
  simp [Nat.factorial]
