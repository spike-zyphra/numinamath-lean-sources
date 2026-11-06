import Mathlib

open Real Set
open scoped Real

theorem algebra_277988 (a b c α β : ℝ)
  (h₀ : a * cos α + b * sin α = c)
  (h₁ : a * cos β + b * sin β = 0)
  (h₂ : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
  sin (α - β) ^ 2 = c ^ 2 / (a ^ 2 + b ^ 2) := by
  have h4 : a ^ 2 + b ^ 2 ≠ 0 := by
    by_contra h
    have ha : a = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, h]
    have hb : b = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, h]
    have h5 : a = 0 ∧ b = 0 ∧ c = 0 := ⟨ha, hb, by
      have eq1 : a * cos α + b * sin α = c := h₀
      have eq2 : a * cos β + b * sin β = 0 := h₁
      have hc1 : c = 0 := by
        rw [ha, hb] at eq1
        nlinarith
      exact hc1
    ⟩
    contradiction

  have h3 : a ^ 2 + b ^ 2 > 0 := by
    by_contra h
    push_neg at h
    have h6 : a ^ 2 + b ^ 2 = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, h]
    have h4' : a ^ 2 + b ^ 2 ≠ 0 := h4
    contradiction

  have eq3 : a * sin (α - β) = -c * sin β := by
    have eq7 : a * sin (α - β) = -c * sin β := by
      have eq8 : sin β * (a * cos α + b * sin α) - sin α * (a * cos β + b * sin β) = sin β * c - sin α * 0 := by
        rw [h₀, h₁]
        <;> nlinarith
      have h9 : sin β * (a * cos α + b * sin α) - sin α * (a * cos β + b * sin β) = a * (sin β * cos α - sin α * cos β) := by
        ring_nf
      have h10 : sin β * cos α - sin α * cos β = -sin (α - β) := by
        have h11 : sin β * cos α - sin α * cos β = sin (β - α) := by
          rw [show β - α = β + (-α) by ring]
          rw [sin_add]
          simp [sin_neg, cos_neg]
          all_goals ring_nf
        have h12 : sin (β - α) = -sin (α - β) := by
          have h13 : β - α = - (α - β) := by ring
          rw [h13]
          rw [sin_neg]
        have eq6 : sin β * cos α - sin α * cos β = -sin (α - β) := by
          linarith [h11, h12]
        exact eq6
      have eq8' : a * -sin (α - β) = c * sin β := by
        rw [h9, h10] at eq8
        linarith
      linarith
    exact eq7

  have eq5 : b * sin (α - β) = c * cos β := by
    have eq6 : b * sin (α - β) = c * cos β := by
      have eq8 : a * cos α + b * sin α = c := h₀
      have eq9 : a * cos β + b * sin β = 0 := h₁
      have eq11 : cos β * (a * cos α + b * sin α) - cos α * (a * cos β + b * sin β) = cos β * c - cos α * 0 := by
        rw [h₀, h₁]
        <;> nlinarith
      have h12 : cos β * (a * cos α + b * sin α) - cos α * (a * cos β + b * sin β) = b * (cos β * sin α - cos α * sin β) := by
        ring_nf
      have h13 : cos β * sin α - cos α * sin β = sin (α - β) := by
        have h14 : cos β * sin α - cos α * sin β = sin (α - β) := by
          rw [show α - β = α + (-β) by ring]
          rw [sin_add]
          simp [sin_neg, cos_neg]
          all_goals ring_nf
          <;> nlinarith
        exact h14
      rw [h12, h13] at eq11
      linarith
    exact eq6

  have eq7 : a ^ 2 * sin (α - β) ^ 2 = c ^ 2 * sin β ^ 2 := by
    calc
      a ^ 2 * sin (α - β) ^ 2 = (a * sin (α - β)) ^ 2 := by ring
      _ = (-c * sin β) ^ 2 := by rw [eq3]
      _ = c ^ 2 * sin β ^ 2 := by ring

  have eq8 : b ^ 2 * sin (α - β) ^ 2 = c ^ 2 * cos β ^ 2 := by
    calc
      b ^ 2 * sin (α - β) ^ 2 = (b * sin (α - β)) ^ 2 := by ring
      _ = (c * cos β) ^ 2 := by rw [eq5]
      _ = c ^ 2 * cos β ^ 2 := by ring

  have eq9 : (a ^ 2 + b ^ 2) * sin (α - β) ^ 2 = c ^ 2 * (sin β ^ 2 + cos β ^ 2) := by
    have eq10 : a ^ 2 * sin (α - β) ^ 2 = c ^ 2 * sin β ^ 2 := by linarith [eq7]
    have eq11 : b ^ 2 * sin (α - β) ^ 2 = c ^ 2 * cos β ^ 2 := by linarith [eq8]
    nlinarith [eq10, eq11]

  have eq12 : (a ^ 2 + b ^ 2) * sin (α - β) ^ 2 = c ^ 2 := by
    have eq13 : sin β ^ 2 + cos β ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq β
    nlinarith [eq9, eq13]

  have eq13 : sin (α - β) ^ 2 = c ^ 2 / (a ^ 2 + b ^ 2) := by
    have eq14 : (a ^ 2 + b ^ 2) * sin (α - β) ^ 2 = c ^ 2 := eq12
    have eq15 : sin (α - β) ^ 2 = c ^ 2 / (a ^ 2 + b ^ 2) := by
      have h1 : a ^ 2 + b ^ 2 ≠ 0 := h4
      field_simp [h1]
      all_goals nlinarith [eq14, h1, sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg c]
    exact eq15

  exact eq13