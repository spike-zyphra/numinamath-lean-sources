import Mathlib

open Equiv Finset

/- 5. (CZS) Solve the following system of equations:  $$ \begin{aligned} & \left|a_{1}-a_{2}\right| x_{2}+\left|a_{1}-a_{3}\right| x_{3}+\left|a_{1}-a_{4}\right| x_{4}=1, \\ & \left|a_{2}-a_{1}\right| x_{1}+\left|a_{2}-a_{3}\right| x_{3}+\left|a_{2}-a_{4}\right| x_{4}=1, \\ & \left|a_{3}-a_{1}\right| x_{1}+\left|a_{3}-a_{2}\right| x_{2}+\left|a_{3}-a_{4}\right| x_{4}=1, \\ & \left|a_{4}-a_{1}\right| x_{1}+\left|a_{4}-a_{2}\right| x_{2}+\left|a_{4}-a_{3}\right| x_{3}=1, \end{aligned} $$  where $a_{1}, a_{2}, a_{3}$, and $a_{4}$ are mutually distinct real numbers. -/
theorem algebra_24599 {a : Fin 4 → ℝ} (ha : ∀ i j, i ≠ j → a i ≠ a j) :
    ∃! σ : Perm (Fin 4), StrictMono (a ∘ σ) ∧
    {x : Fin 4 → ℝ |
      |a 0 - a 1| * x 1 + |a 0 - a 2| * x 2 + |a 0 - a 3| * x 3 = 1 ∧
      |a 1 - a 0| * x 0 + |a 1 - a 2| * x 2 + |a 1 - a 3| * x 3 = 1 ∧
      |a 2 - a 0| * x 0 + |a 2 - a 1| * x 1 + |a 2 - a 3| * x 3 = 1 ∧
      |a 3 - a 0| * x 0 + |a 3 - a 1| * x 1 + |a 3 - a 2| * x 2 = 1} =
    {x : Fin 4 → ℝ |
      x (σ 0) = 1 / (a (σ 3) - a (σ 0)) ∧
      x (σ 1) = 0 ∧
      x (σ 2) = 0 ∧
      x (σ 3) = 1 / (a (σ 3) - a (σ 0))} := by

  -- We prove that the system of equations has a unique solution up to the permutation of the variables.
  -- We first construct a permutation σ such that a ∘ σ is strictly increasing.
  have ha_inj : Function.Injective a := by
    intro i j hij
    by_contra h
    apply ha at h
    exact h.elim hij

  let s : Finset ℝ := univ.image a
  have hs : s.card = 4 := by
    simp [s]
    rw [card_image_of_injective]
    · simp
    · exact ha_inj

  let f (i : Fin 4) : s := ⟨a i, by simp [s]⟩
  have hf : Function.Bijective f := by
    apply Nat.bijective_iff_injective_and_card _ |>.mpr
    constructor
    · intro i j hij
      simp [f] at hij
      exact ha_inj hij
    · simp [hs]

  let φ : Fin 4 ≃ s := by apply Equiv.ofBijective f hf

  have hφ {x : s} : a (φ.symm x) = x := by
    have {i : Fin 4} : a i = φ i := by simp [φ]
    rw [this]
    simp only [apply_symm_apply]

  obtain ⟨g, hiso⟩ := orderIsoOfFin s hs
  have hg_mono : StrictMono g := by
    apply Monotone.strictMono_of_injective
    · intro a b hab
      apply hiso.mpr hab
    · exact Equiv.injective g

  let σ : Fin 4 ≃ Fin 4 := Equiv.trans g (Equiv.symm φ)

  have hσ : StrictMono (a ∘ ⇑σ) := by
    intro i j hij
    simp [σ]
    rw [hφ, hφ]
    simp
    apply hg_mono hij

  -- Then under this permutation, the system of equations has a unique solution.
  use σ
  constructor
  · -- Firstly, we prove that the system of equations becomes a system of equations with the form
    -- ∑ _{j}, |a (σ i) - a (σ j)| * x (σ j) = 1. for all i
    simp [hσ]
    have ha {i j : Fin 4} (h : i ≠ j) : a (σ i) - a (σ j) ≠ 0 := by
      intro h
      apply sub_eq_zero.mp at h
      apply StrictMono.injective hσ at h
      contradiction
    have h₀ : {x : Fin 4 → ℝ |
        |a 0 - a 1| * x 1 + |a 0 - a 2| * x 2 + |a 0 - a 3| * x 3 = 1 ∧
        |a 1 - a 0| * x 0 + |a 1 - a 2| * x 2 + |a 1 - a 3| * x 3 = 1 ∧
        |a 2 - a 0| * x 0 + |a 2 - a 1| * x 1 + |a 2 - a 3| * x 3 = 1 ∧
        |a 3 - a 0| * x 0 + |a 3 - a 1| * x 1 + |a 3 - a 2| * x 2 = 1} =
        {x : Fin 4 → ℝ |
        |a (σ 0) - a (σ 1)| * x (σ 1) + |a (σ 0) - a (σ 2)| * x (σ 2) + |a (σ 0) - a (σ 3)| * x (σ 3) = 1 ∧
        |a (σ 0) - a (σ 1)| * x (σ 0) + |a (σ 1) - a (σ 2)| * x (σ 2) + |a (σ 1) - a (σ 3)| * x (σ 3) = 1 ∧
        |a (σ 0) - a (σ 2)| * x (σ 0) + |a (σ 1) - a (σ 2)| * x (σ 1) + |a (σ 2) - a (σ 3)| * x (σ 3) = 1 ∧
        |a (σ 0) - a (σ 3)| * x (σ 0) + |a (σ 1) - a (σ 3)| * x (σ 1) + |a (σ 2) - a (σ 3)| * x (σ 2) = 1} := by
      ext x
      simp
      have : |a 0 - a 1| * x 1 + |a 0 - a 2| * x 2 + |a 0 - a 3| * x 3 = 1 ∧
          |a 1 - a 0| * x 0 + |a 1 - a 2| * x 2 + |a 1 - a 3| * x 3 = 1 ∧
          |a 2 - a 0| * x 0 + |a 2 - a 1| * x 1 + |a 2 - a 3| * x 3 = 1 ∧
          |a 3 - a 0| * x 0 + |a 3 - a 1| * x 1 + |a 3 - a 2| * x 2 = 1 ↔
          ∀ i, ∑ j : Fin 4, |a i - a j| * x j = 1 := by
        constructor <;> intro h
        · obtain ⟨h₁, h₂, h₄, h₅⟩ := h
          intro i
          fin_cases i
          all_goals
            simp [Fin.sum_univ_four]
            assumption
        · simp [Fin.sum_univ_four] at h
          split_ands
          · rw [←h 0]
            simp
          · rw [←h 1]
            simp
          · rw [←h 2]
            simp
          · rw [←h 3]
            simp
      apply Iff.trans this
      have : (∀ i, ∑ j : Fin 4, |a i - a j| * x j = 1) ↔
          ∀ i, ∑ j : Fin 4, |a (σ i) - a (σ j)| * x (σ j) = 1 := by
        constructor <;> intro h
        · intro i
          rw [←h]
          have : univ.image σ = univ := by
            exact image_univ_equiv σ
          nth_rw 2 [←this]
          rw [sum_image]
          intro x _ y _ h
          apply Equiv.injective σ h
        · intro i
          obtain h := h (σ.symm i)
          simp at h
          rw [←h]
          have : univ.image σ = univ := by
            exact image_univ_equiv σ
          nth_rw 1 [←this]
          rw [sum_image]
          intro x _ y _ h
          apply Equiv.injective σ h
      apply Iff.trans this
      constructor <;> intro h
      · split_ands
        · rw [←h (i := 0)]
          simp [Fin.sum_univ_four]
        · rw [←h (i := 1)]
          simp [Fin.sum_univ_four]
          left
          exact abs_sub_comm (a (σ 0)) (a (σ 1))
        · rw [←h (i := 2)]
          simp [Fin.sum_univ_four]
          congr 1
          all_goals rw [abs_sub_comm]
        · rw [←h (i := 3)]
          simp [Fin.sum_univ_four]
          congr 1
          any_goals rw [abs_sub_comm]
          congr 1
          any_goals rw [abs_sub_comm]
      · intro i
        obtain ⟨h₁, h₂, h₃, h₄⟩ := h
        fin_cases i
        all_goals simp [Fin.sum_univ_four]
        · rw [←h₁]
        · rw [←h₂]
          congr 1
          rw [abs_sub_comm]
        · rw [←h₃]
          congr 1
          congr 1
          all_goals rw [abs_sub_comm]
        · rw [←h₄]
          congr 1
          congr 1
          all_goals rw [abs_sub_comm]
    rw [h₀]
    -- Note that a ∘ σ is strictly increasing, so we have a (σ 0) < a (σ 1) < a (σ 2) < a (σ 3).
    -- Therefore, we can simplify the abs in the equations.
    rw [abs_of_neg, abs_of_neg, abs_of_neg, abs_of_neg, abs_of_neg, abs_of_neg]
    · ext x
      simp
      -- solve the system of equations
      -- We obtain that x (σ 0) = 1 / (a (σ 3) - a (σ 0)), x (σ 1) = 0, x (σ 2) = 0, and x (σ 3) = 1 / (a (σ 3) - a (σ 0)).
      constructor <;> intro ⟨h₁, h₂, h₃, h₄⟩
      · have h₅ : (a (σ 1) - a (σ 0)) * x (σ 0) - (a (σ 1) - a (σ 0)) * x (σ 1) - (a (σ 1) - a (σ 0)) * x (σ 2) - (a (σ 1) - a (σ 0)) * x (σ 3) = 0 := by linear_combination h₂ - h₁
        rw [←mul_sub, ←mul_sub, ←mul_sub] at h₅
        simp at h₅
        simp [ha] at h₅
        have h₆ : (a (σ 2) - a (σ 1)) * x (σ 0) + (a (σ 2) - a (σ 1)) * x (σ 1) - (a (σ 2) - a (σ 1)) * x (σ 2) - (a (σ 2) - a (σ 1)) * x (σ 3) = 0 := by linear_combination h₃ - h₂
        rw [←mul_add, ←mul_sub, ←mul_sub] at h₆
        simp at h₆
        simp [ha] at h₆
        have h₇ : x (σ 1) = 0 := by linear_combination (h₆ - h₅) / 2
        simp [h₇] at h₁ h₃ h₄ h₅ ⊢
        have h₈ : (a (σ 3) - a (σ 2)) * x (σ 0) + (a (σ 3) - a (σ 2)) * x (σ 2) - (a (σ 3) - a (σ 2)) * x (σ 3) = 0 := by linear_combination h₄ - h₃
        rw [←mul_add, ←mul_sub] at h₈
        simp at h₈
        simp [ha] at h₈
        have h₉ : x (σ 2) = 0 := by linear_combination (h₈ - h₅) / 2
        simp [h₉] at h₅ h₁ ⊢
        apply sub_eq_zero.mp at h₅
        simp [h₅]
        field_simp [ha]
        rw [←h₁]
        ring
      · simp [h₁, h₂, h₃, h₄]
        field_simp
        rw [div_self]
        apply ne_of_gt
        simp
        apply hσ
        simp
    all_goals
      simp
      apply hσ
      simp
  · -- We also prove that this permutation is unique.
    intro π ⟨hπ, _⟩
    ext i
    have : (a ∘ π) i = (a ∘ σ) i := by
      have hf {f : Fin 4 ≃ Fin 4} (i : Fin 4) (hf : StrictMono (a ∘ f)) : (s.filter (fun x => x < (a ∘ f) i)).card = i := by
        let a (x : ℕ) (hi : x < i) := a (f ⟨x, lt_trans hi i.2⟩)
        apply card_eq_of_bijective a
        · simp [s, a]
          intro x hlt
          use f.symm x
          constructor
          · simp
          · apply StrictMono.lt_iff_lt hf |>.mp
            simp
            exact hlt
        · simp [a, s]
          intro x hx
          apply StrictMono.lt_iff_lt hf |>.mpr hx
        · simp [a, s]
          intro x y _ _ hxy
          apply StrictMono.injective hf at hxy
          simp at hxy
          exact hxy
      apply hf i at hπ
      apply hf i at hσ
      rw [←hπ] at hσ
      by_contra h
      simp at h
      rcases lt_or_gt_of_ne h with h | h
      · have : #(filter (fun x => x < (a ∘ ⇑σ) i) s) > #(filter (fun x => x < (a ∘ ⇑π) i) s) := by
          apply card_lt_card
          constructor
          · intro x hx
            simp at hx ⊢
            constructor
            · exact hx.1
            · apply lt_trans hx.2
              exact h
          · apply Finset.not_subset.mpr
            use (a ∘ ⇑π) i
            simp [s, h]
        rw [hσ] at this
        simp at this
      · have : #(filter (fun x => x < (a ∘ ⇑σ) i) s) < #(filter (fun x => x < (a ∘ ⇑π) i) s) := by
          apply card_lt_card
          constructor
          · intro x hx
            simp at hx ⊢
            constructor
            · exact hx.1
            · apply lt_trans hx.2
              exact h
          · apply Finset.not_subset.mpr
            use (a ∘ ⇑σ) i
            simp [s, h]
        rw [hσ] at this
        simp at this
    simp at this
    apply ha_inj at this
    simp [this]
