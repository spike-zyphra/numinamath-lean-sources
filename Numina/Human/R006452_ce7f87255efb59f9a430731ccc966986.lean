import Mathlib
open Finset Set Nat Polynomial Finsupp
noncomputable section

def S (A : Finset ℝ) (c : ℝ) : Finset ℝ := A.image (fun x => (x - c) / x)

/-Let $c$ be a positive real number. Let $A$ be a finite non-empty set of real numbers such that for every $x \in A$, $x > c$. Define the set $S = \{ (x-c)/x \mid x \in A \}$. Determine the maximum element of $S$. Show the answer is $(\max(A)-c)/\max(A)$, where $\max(A)$ denotes the maximum element in $A$.-/
theorem number_theory_637231 (c : ℝ) (hc : c > 0) (A : Finset ℝ) (hA_nonempty : A.Nonempty)
    (hA_pos : ∀ x ∈ A, x > c) :
    max' (S A c) (by
      obtain ⟨x, hx⟩ := hA_nonempty
      exact ⟨(x - c) / x, mem_image.mpr ⟨x, hx, rfl⟩⟩
    ) = (A.max' hA_nonempty - c) / A.max' hA_nonempty := by
  -- Define $f(x)$.
  let f : ℝ → ℝ := fun x => (x - c) / x
  -- Define the function $f(x) = (x - c) / x$.
  have h_f_def : ∀ x ∈ A, f x = (x - c) / x := by simp [f]
  -- Prove that $f(x)$ is strictly increasing for $x > c$.
  have h_f_increasing : ∀ x y, c < x → x < y → f x < f y := by
    intros x y h_xc h_xy
    have h_x_pos : x > 0 := lt_trans hc h_xc
    have h_y_pos : y > 0 := lt_trans h_x_pos h_xy
    simp [f]
    have h_c_inv : c / x > c / y := by
      exact (div_lt_div_iff_of_pos_left hc h_y_pos h_x_pos).mpr h_xy
    have : (x - c) / x < (y - c) / y := by
      have : (x - c) / x = 1 - c / x := by rw [same_sub_div (by nlinarith)]
      have : (y - c) / y = 1 - c / y := by rw [same_sub_div (by nlinarith)]
      nlinarith
    exact this
  -- Prove that for all $x ∈ A$, $f(x) ≤ f(max(A))$.
  have h_f_max : ∀ x ∈ A, f x ≤ f (A.max' hA_nonempty) := by
    intro x h_x
    have h_xm : x ≤ A.max' hA_nonempty := le_max' A x h_x
    have h_xm_le : x < A.max' hA_nonempty ∨ x = A.max' hA_nonempty := lt_or_eq_of_le h_xm
    have h_x_c : c < x := hA_pos x h_x
    have h_xm_c : c < A.max' hA_nonempty := hA_pos (A.max' hA_nonempty) (max'_mem A hA_nonempty)
    rcases h_xm_le with (h_x_lt | h_x_eq)
    · exact (h_f_increasing x (A.max' hA_nonempty) h_x_c h_x_lt).le
    · simp [h_x_eq]
  -- Prove that $f(max(A)) ∈ S$ and is the maximum element.
  have h_f_max_in_S : f (A.max' hA_nonempty) ∈ S A c := by
    simp [S, Finset.mem_image, f]
    exact ⟨A.max' hA_nonempty, max'_mem A hA_nonempty, rfl⟩
  have h_max_S : max' (S A c) (by
    obtain ⟨x, hx⟩ := hA_nonempty
    exact ⟨(x - c) / x, mem_image.mpr ⟨x, hx, rfl⟩⟩
  ) = f (A.max' hA_nonempty) := by
    apply le_antisymm
    · apply max'_le
      intro y h_y
      simp [S, Finset.mem_image] at h_y
      obtain ⟨x, h_x, h_y⟩ := h_y
      rw [← h_y]
      exact h_f_max x h_x
    · apply le_max' _ _ h_f_max_in_S
  -- Express the result as $(max(A) - c) / max(A)$.
  have h_result : f (A.max' hA_nonempty) = (A.max' hA_nonempty - c) / A.max' hA_nonempty := by
    simp [f]
  rw [h_max_S, h_result]
