import Mathlib

open Complex

/- A root independent of λ must be the common root of equation x ^ 5 - x ^ 3 - 4 x ^ 2 - 3x-2 = 0 and 5 x ^ 4 + α x ^ 2 - 8 x + α = 0 -/
lemma common_root_eq_inter {α : ℂ} :
    {x : ℂ | ∀ lambda, x^5 + 5 * lambda * x^4 - x^3 + (lambda * α - 4) * x^2 - (8 * lambda + 3) * x + lambda * α - 2 = 0} =
    {x : ℂ | x ^ 5 - x ^ 3 - 4 * x ^ 2 - 3 * x - 2 = 0} ∩ {x : ℂ | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0} := by

  -- 43. We can write the given equation in the form
  -- $$ x^{5}-x^{3}-4 x^{2}-3 x-2+\lambda\left(5 x^{4}+\alpha x^{2}-8 x+\alpha\right)=0 . $$ A root of this equation is
  have heq {x lambda : ℂ} :
      x^5 + 5 * lambda * x^4 - x^3 + (lambda * α - 4) * x^2 - (8 * lambda + 3) * x + lambda * α - 2 =
      x ^ 5 - x ^ 3 - 4 * x ^ 2 - 3 * x - 2 + lambda * (5 * x ^ 4 + α * x ^ 2 - 8 * x + α) := by
    ring
  simp [heq]
  ext x
  simp
  constructor <;> intro hx
  · -- If x is a root independent of λ, then it must satisfy the equation for λ = 0
    obtain h₀ := hx 0
    simp at h₀
    -- Therefore, x ^ 5 - x ^ 3 - 4 * x ^ 2 - 3 * x - 2 = 0
    simp [h₀] at hx ⊢
    -- let λ = 0, we have 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0
    obtain h₁ := hx 1
    simp at h₁
    simp [h₁]
  · -- The other direction is straightforward.
    simp [hx]

/- Solve the equation x ^ 5 - x ^ 3 - 4 * x ^ 2 - 3 * x - 2 = 0 -/
lemma root_of_left : {x : ℂ| x ^ 5 - x ^ 3 - 4 * x ^ 2 - 3 * x - 2 = 0} = ({(2 : ℂ), (-1 + √3 * I) / 2, (-1 - √3 * I) / 2} : Set ℂ) := by
  ext x
  simp
  -- Decompose the polynomial x ^ 5 - x ^ 3 - 4 * x ^ 2 - 3 * x - 2 = (x - 2) * (x ^ 2 + x + 1) ^ 2
  have heq : x ^ 5 - x ^ 3 - 4 * x ^ 2 - 3 * x - 2 = (x - 2) * (x ^ 2 + x + 1) ^ 2 := by
    ring
  rw [heq]
  -- NOte that x ^ 2 + x + 1 = (x - (-1 + ↑√3 * I) / 2) * (x - (-1 - ↑√3 * I) / 2)
  have heq : x ^ 2 + x + 1 = (x - (-1 + ↑√3 * I) / 2) * (x - (-1 - ↑√3 * I) / 2) := by
    ring_nf
    rw [←ofReal_pow, Real.sq_sqrt, I_sq]
    simp
    ring_nf
    simp
  rw [heq]
  simp
  -- Therefore, the roots are 2, (-1 + √3 * I) / 2 and (-1 - √3 * I) / 2
  constructor <;> intro hx
  · rcases hx with h | h | h
    · apply sub_eq_zero.mp at h
      simp [h]
    · apply sub_eq_zero.mp at h
      simp [h]
    · apply sub_eq_zero.mp at h
      simp [h]
  · rcases hx with hx | hx | hx
    · simp [hx]
    · simp [hx]
    · simp [hx]

/- If 2 is a root of the right equation, then α = -64/5 ∧ the intersection is exactly {2} -/
lemma inter_of_two_mem {α : ℂ} (h : 2 ∈ {x | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0}) :
    α = -64 / 5 ∧ {2, (-1 + ↑√3 * I) / 2, (-1 - ↑√3 * I) / 2} ∩ {x | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0} = {2} := by
  -- Substituting x = 2 into the equation 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0
  -- We obtain that α = -64 / 5
  simp at h
  norm_num at h
  ring_nf at h
  have : α = -64 / 5 := by
    field_simp
    apply sub_eq_zero.mp
    rw [←h]
    ring
  -- Substituting α = -64 / 5 into the equation
  -- 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0
  constructor
  · exact this
  · -- It is easy to see that (-1 + ↑√3 * I) / 2, (-1 - ↑√3 * I) / 2 are not roots of the equation
    -- Therefore, the intersection is exactly {2}
    simp [this]
    field_simp
    have {x : ℂ} : 5 * x ^ 4 * 5 + -(64 * x ^ 2) - 5 * (8 * x) + -64 = (x - 2) * (25 * x ^ 3 + 50 * x ^ 2 + 36 * x + 32) := by
      ring
    simp [this]
    ext x
    simp
    have hsqrt : √3 ^ 3 = 3 * √3 := by
      rw [show 3 = 2 + 1 by simp]
      rw [pow_add, Real.sq_sqrt]
      ring
      simp
    have hI : I ^ 3 = - I := by
      rw [show 3 = 2 + 1 by simp]
      rw [pow_add, I_sq]
      simp
    constructor <;> intro hx
    · obtain ⟨h₁, h₂⟩ := hx
      rcases h₁ with h₁ | h₁ | h₁
      · exact h₁
      · have : x - 2 ≠ 0 := by
          simp [h₁]
          by_contra h
          apply congrArg re at h
          simp at h
          norm_num at h
        simp [this] at h₂
        have : ¬ 25 * x ^ 3 + 50 * x ^ 2 + 36 * x + 32 = 0 := by
          simp [h₁]
          ring_nf
          field_simp
          simp [←ofReal_pow, hsqrt, hI]
          by_contra h
          apply congrArg re at h
          simp at h
          norm_num at h
        contradiction
      · have : x - 2 ≠ 0 := by
          simp [h₁]
          by_contra h
          apply congrArg re at h
          simp at h
          norm_num at h
        simp [this] at h₂
        have : ¬ 25 * x ^ 3 + 50 * x ^ 2 + 36 * x + 32 = 0 := by
          simp [h₁]
          ring_nf
          field_simp
          simp [←ofReal_pow, hsqrt, hI]
          by_contra h
          apply congrArg re at h
          simp at h
          norm_num at h
        contradiction
    · simp [hx]

/- If (-1 + ↑√3 * I) / 2 or (-1 - √3 * I) / 2 is a root of the right equation, then α = -3, and the intersection are exactly these two roots. -/
lemma inter_of_neg_one_add_mem {α : ℂ} (h : (-1 + ↑√3 * I) / 2 ∈ {x | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0} ∨ (-1 - ↑√3 * I) / 2 ∈ {x | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0}) :
    α = -3 ∧ {2, (-1 + ↑√3 * I) / 2, (-1 - ↑√3 * I) / 2} ∩ {x | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0} = {(-1 + ↑√3 * I) / 2, (-1 - ↑√3 * I) / 2} := by
  -- Some auxiliary calculations
  have hsqrt_sq : (√3 : ℂ) ^ 2 = 3 := by
    rw [←ofReal_pow, Real.sq_sqrt]
    norm_num
    simp
  have hsqrt_three : (√3 : ℂ) ^ 3 = 3 * √3 := by
    rw [show 3 = 2 + 1 by simp]
    rw [pow_add, hsqrt_sq]
    ring
  have hsqrt_four : (√3 : ℂ) ^ 4 = 9 := by
    rw [show 4 = 2 + 2 by simp]
    rw [pow_add, hsqrt_sq]
    norm_num
  have hI : I ^ 3 = - I := by
    rw [show 3 = 2 + 1 by simp]
    rw [pow_add, I_sq]
    simp
  -- Directly substituting (-1 + √3 * I) / 2 or (-1 - √3 * I) / 2 into the equation.
  simp at h
  ring_nf at h
  simp [hsqrt_sq, hsqrt_three, hsqrt_four, hI] at h
  norm_num at h
  -- It is not difficult to see that α.re = -3 and α.im = 0
  have hα : α.im = 0 ∧ α.re = -3 := by
    rcases h with h | h
    · obtain h₁ := congrArg re h
      obtain h₂ := congrArg im h
      simp at h₁ h₂
      ring_nf at h₁ h₂
      norm_num at h₁ h₂
      obtain h : (3 / 2 + √3 * α.im * (1 / 2) + α.re * (1 / 2)) * √3 + -(√3 * (3 / 2)) + -(√3 * α.re * (1 / 2)) + α.im * (1 / 2) = 0 := by
        linear_combination h₁ * √3 + h₂
      ring_nf at h
      rw [Real.sq_sqrt (by simp)] at h
      have him : α.im = 0 := by linear_combination h * (1 / 2)
      simp [him] at h₁
      have hre : α.re = -3 := by
        linear_combination h₁ * 2
      exact ⟨him, hre⟩
    · obtain h₁ := congrArg re h
      obtain h₂ := congrArg im h
      simp at h₁ h₂
      ring_nf at h₁ h₂
      norm_num at h₁ h₂
      obtain h : (3 / 2 + -√3 * α.im * (1 / 2) + α.re * (1 / 2)) * √3 - ((√3 * (3 / 2)) + (√3 * α.re * (1 / 2)) + α.im * (1 / 2)) = 0 := by
        linear_combination h₁ * √3 - h₂
      ring_nf at h
      rw [Real.sq_sqrt (by simp)] at h
      ring_nf at h
      have him : α.im = 0 := by linear_combination h * (-1 / 2)
      simp [him] at h₁
      have hre : α.re = -3 := by
        linear_combination h₁ * 2
      exact ⟨him, hre⟩
  -- Therefore, α = -3
  have hα : α = -3 := by
    apply ext
    · simp [hα.2]
    · simp [hα.1]

  -- substituting α = -3 into the equation
  constructor
  · exact hα
  · simp [hα]
    -- The equation becomes (x ^ 2 + x + 1) * (5 * x ^ 2 - 5 * x - 3) = 0
    have {x : ℂ} : 5 * x ^ 4 + -(3 * x ^ 2) - 8 * x + -3 = (x ^ 2 + x + 1) * (5 * x ^ 2 - 5 * x - 3) := by
      ring
    simp [this]
    have heq {x : ℂ} : x ^ 2 + x + 1 = (x - (-1 + ↑√3 * I) / 2) * (x - (-1 - ↑√3 * I) / 2) := by
      ring_nf
      rw [←ofReal_pow, Real.sq_sqrt, I_sq]
      simp
      ring_nf
      simp
    simp [heq]
    ext x
    simp
    constructor <;> intro hx
    · obtain ⟨h₀, h⟩ := hx
      rcases h with (h | h) | h
      · apply sub_eq_zero.mp at h
        simp [h]
      · apply sub_eq_zero.mp at h
        simp [h]
      · -- 2, (-1 + √3 * I) / 2 or (-1 - √3 * I) / 2 is not a root of 5 * x ^ 2 - 5 * x - 3 = 0.
        -- Therefore, we can conclude that the intersection is exactly {(-1 + √3 * I) / 2, (-1 - √3 * I) / 2}
        have : ¬ x = 2 := by
          by_contra h'
          simp [h'] at h
          norm_num at h
        simp [this] at h₀
        have : ¬ x = (-1 + ↑√3 * I) / 2 := by
          by_contra h'
          simp [h'] at h
          ring_nf at h
          simp [hsqrt_sq] at h
          apply congrArg im at h
          simp at h
        simp [this] at h₀
        have : ¬ x = (-1 - ↑√3 * I) / 2 := by
          by_contra h'
          simp [h'] at h
          ring_nf at h
          simp [hsqrt_sq] at h
          apply congrArg im at h
          simp at h
        contradiction
    · rcases hx with hx | hx
      · simp [hx]
      · simp [hx]

/- 43. (ROM 2) The equation  $$ x^{5}+5 \lambda x^{4}-x^{3}+(\lambda \alpha-4) x^{2}-(8 \lambda+3) x+\lambda \alpha-2=0 $$  is given.
(a) Determine $\alpha$ such that the given equation has exactly one root independent of $\lambda$.
(b) Determine $\alpha$ such that the given equation has exactly two roots independent of $\lambda$. -/
theorem algebra_24703 {common_root : ℂ → Set ℂ}
    (hroot : ∀ α, common_root α = {x : ℂ | ∀ lambda, x^5 + 5 * lambda * x^4 - x^3 + (lambda * α - 4) * x^2 - (8 * lambda + 3) * x + lambda * α - 2 = 0}) :
    {α : ℂ | (common_root α).ncard = 1} = {-64/5} ∧ {α : ℂ | (common_root α).ncard = 2} = {-3} := by

  -- Apply our lemmas to simplify the result.
  simp [common_root_eq_inter] at hroot
  simp [root_of_left] at hroot
  simp [hroot]

  constructor
  · -- If the given equation has exactly one root independent of λ, then it must be 2, (-1 + √3*I) /2 or (-1-√3 *I)/2
    ext α
    simp
    constructor <;> intro hα
    · obtain ⟨a, ha⟩ := hα
      have : a ∈ ({a} : Set _) := by simp
      simp [←ha] at this
      rcases this.1 with h | h | h
      · -- If it is 2, then we are done by lemma inter_of_two_mem
        simp [h] at this
        apply (inter_of_two_mem this).1
      · -- If it is (-1 + √3 * I) / 2, then the intersection contains two roots, which is a contradiction.
        simp [h] at this
        obtain h : {2, (-1 + ↑√3 * I) / 2, (-1 - ↑√3 * I) / 2} ∩ {x | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0} = {(-1 + √3*I) /2, (-1-√3 *I)/2} := by
          apply (inter_of_neg_one_add_mem ?_).2
          left
          simp [this]
        simp [h] at ha
        have h₁ : (-1 + √3 * I) / 2 ∈ ({a} : Set ℂ) := by
          simp [←ha]
        simp at h₁
        have h₂ : (-1 - √3 * I) / 2 ∈ ({a} : Set ℂ) := by
          simp [←ha]
        simp at h₂
        simp [←h₁] at h₂
        apply congrArg im at h₂
        simp at h₂
        rw [eq_comm] at h₂
        apply sub_eq_zero.mpr at h₂
        ring_nf at h₂
        simp at h₂
      · -- If the root is (-1 - √3 * I) / 2, then the intersection contains two roots, which is a contradiction.
        simp [h] at this
        obtain h : {2, (-1 + ↑√3 * I) / 2, (-1 - ↑√3 * I) / 2} ∩ {x | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0} = {(-1 + √3*I) /2, (-1-√3 *I)/2} := by
          apply (inter_of_neg_one_add_mem ?_).2
          right
          simp [this]
        simp [h] at ha
        have h₁ : (-1 - √3 * I) / 2 ∈ ({a} : Set ℂ) := by
          simp [←ha]
        simp at h₁
        have h₂ : (-1 + √3 * I) / 2 ∈ ({a} : Set ℂ) := by
          simp [←ha]
        simp at h₂
        simp [←h₁] at h₂
        apply congrArg im at h₂
        simp at h₂
        rw [eq_comm] at h₂
        apply sub_eq_zero.mpr at h₂
        ring_nf at h₂
        simp at h₂
    · -- If α = -64 / 5, then the result is easy to see.
      use 2
      apply (inter_of_two_mem ?_).2
      simp [hα]
      norm_num
  · -- Some auxiliary calculations
    have hsqrt_sq : (√3 : ℂ) ^ 2 = 3 := by
      rw [←ofReal_pow, Real.sq_sqrt]
      norm_num
      simp
    have hsqrt_three : (√3 : ℂ) ^ 3 = 3 * √3 := by
      rw [show 3 = 2 + 1 by simp]
      rw [pow_add, hsqrt_sq]
      ring
    have hsqrt_four : (√3 : ℂ) ^ 4 = 9 := by
      rw [show 4 = 2 + 2 by simp]
      rw [pow_add, hsqrt_sq]
      norm_num
    have hI : I ^ 3 = - I := by
      rw [show 3 = 2 + 1 by simp]
      rw [pow_add, I_sq]
      simp
    ext α
    simp
    constructor <;> intro hα
    · -- If there exist two roots, then one of them must be 2, (-1 + √3 * I) / 2 or (-1 - √3 * I) / 2
      obtain ⟨a, ha⟩ : ({2, (-1 + ↑√3 * I) / 2, (-1 - ↑√3 * I) / 2} ∩ {x | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0}).Nonempty := by
        apply Set.nonempty_of_ncard_ne_zero
        simp [hα]
      simp at ha
      obtain ⟨ha, ha'⟩ := ha
      rcases ha with h | h | h
      · -- If it is 2, then by lemma inter_of_two_mem, we have α = -64 / 5 and the intersection is exactly {2}, which is a contradiction.
        obtain h : {2, (-1 + ↑√3 * I) / 2, (-1 - ↑√3 * I) / 2} ∩ {x | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0} = {2} := by
          apply (inter_of_two_mem ?_).2
          simp [hα]
          simp [h] at ha'
          exact ha'
        simp [h] at hα
      · -- If it is (-1 + √3 * I) / 2, then we are done by lemma inter_of_neg_one_add_mem
        apply (inter_of_neg_one_add_mem ?_).1
        left
        simp [h] at ha'
        exact ha'
      · -- If the root is (-1 - √3 * I) / 2, the proof proceeds similarly to the previous case.
        apply (inter_of_neg_one_add_mem ?_).1
        right
        simp [h] at ha'
        exact ha'
    · -- If α = -3, then (-3 + √3 I) / 2 is a common root, then by our lemma, there exist exactly two roots independent of λ.
      obtain h : ({2, (-1 + ↑√3 * I) / 2, (-1 - ↑√3 * I) / 2} ∩ {x | 5 * x ^ 4 + α * x ^ 2 - 8 * x + α = 0}) = {(-1 + √3*I) /2, (-1-√3 *I)/2} := by
        apply (inter_of_neg_one_add_mem ?_).2
        simp [hα]
        left
        ring_nf
        simp [hsqrt_sq, hsqrt_three, hsqrt_four, hI]
        apply ext
        · simp
          norm_num
        · simp
          ring_nf
      simp [h]
      apply Set.ncard_eq_two.mpr
      -- One has to porve that (-1 - √3 * I) / 2 ≠ (-1 + √3 * I) / 2 to show that the intersection is exactly two roots.
      -- But this is trivial.
      use (-1 + √3 * I) / 2, (-1 - √3 * I) / 2
      simp
      by_contra h
      apply congrArg im at h
      simp at h
      apply sub_eq_zero.mpr at h
      ring_nf at h
      simp at h
