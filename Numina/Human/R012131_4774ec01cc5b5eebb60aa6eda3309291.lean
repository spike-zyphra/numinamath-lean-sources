import Mathlib

open Real Set

/-11.45 For what values of $m$ does the equation $2 \sqrt{1-m(x+2)}=x+4$ have one root?-/
theorem algebra_181161 :
    {m : ℝ | {x : ℝ | 1 - m * (x + 2) ≥ 0 ∧ 2 * √(1 - m * (x + 2)) = x + 4}.ncard = 1} = {-1} ∪ Ioi (-1/2) := by

  have hsol {m : ℝ} : {x : ℝ | 1 - m * (x + 2) ≥ 0 ∧ 2 * √(1 - m * (x + 2)) = x + 4} ⊆ {-2, -4 * m - 6} := by
    intro x hx
    simp at hx ⊢
    -- Если $m=0$, то уравнение примет вид $2=x+4$ и, значит, имеет единственный корень $x=-2$. Пусть $m \neq 0$.
    by_cases hm : m = 0
    · simp [hm] at hx ⊢
      left
      linarith only [hx]
    · -- Положим
      -- $$ \sqrt{1-m(x+2)}=y \geq 0, \quad \text { откуда } \quad \text { после } $$
      let y := √(1 - m * (x + 2))
      -- преобразований найдем $x=\frac{1-y^{2}}{m}-2$. Тогда данное уравнение запишется так:
      have h₁ : x = (1 - y ^ 2) / m - 2 := by
        unfold y
        rw [sq_sqrt]
        · field_simp
        · linarith only [hx.1]

      -- $$ 2 y=\frac{1-y^{2}}{m}-2+4, \text { или } y^{2}+2 m y-1=2 m $$
      have h : 2 * y = x + 4 := hx.2
      have h₂ : (y - 1) * (y - (-(2 * m + 1))) = 0 := by
        rw [h₁] at h
        field_simp at h
        nlinarith only [h]
      simp at h₂
      rcases h₂ with h₂ | h₂
      · have hy : y = 1 := by linarith only [h₂]
        rw [hy] at h
        left
        linarith only [h]
      · have hy : y = -(2 * m + 1) := by linarith only [h₂]
        rw [hy] at h
        right
        linarith only [h]

  ext m
  simp
  by_cases hm : m ≤ -1 / 2
  · -- when m ≤ -1/2, we prove that the roots are -2 and -4m-6
    have : ¬ m > -1/2 := by exact not_lt_of_ge hm
    simp [this]
    have hsub : {-2, -4 * m - 6} ⊆ {x | 1 - m * (x + 2) ≥ 0 ∧ 2 * √(1 - m * (x + 2)) = x + 4} := by
      intro x hx
      simp at hx ⊢
      rcases hx with hx | hx <;> simp [hx]
      · norm_num
      · constructor
        · apply sub_nonneg.mp
          trans (1 + 2 * m) ^ 2
          · positivity
          · apply le_of_eq
            ring
        · have : 1 - m * (-(4 * m) - 6 + 2) = (2 * m + 1) ^ 2 := by ring
          rw [this, sqrt_sq_eq_abs, abs_of_nonpos]
          · ring
          · linarith only [hm]
    have heq : {-2, -4 * m - 6} = {x | 1 - m * (x + 2) ≥ 0 ∧ 2 * √(1 - m * (x + 2)) = x + 4} := by
      apply le_antisymm
      · exact hsub
      · exact hsol
    -- since the equation has only one root, we have $-2=-4 m-6$.
    -- therefore,  $m=-1$.
    constructor <;> intro h
    · obtain ⟨a, ha⟩ := h
      simp [ha] at hsub
      obtain ⟨h₁, h₂⟩ := hsub
      rw [←h₁] at h₂
      linarith only [h₂]
    · use -2
      simp at heq
      rw [←heq, h]
      norm_num
  · -- when m > -1/2, we prove that -2 are the only roots
    simp at hm
    simp [hm]
    use -2
    ext x
    constructor <;> intro h
    · simp at hsol
      obtain h' := hsol h
      simp at h'
      rcases h' with h' | h'
      · simp [h']
      · simp [h'] at h
        obtain h := h.2
        rw [show 1 - m * (-(4 * m) - 6 + 2) = (2 * m + 1) ^ 2 by ring] at h
        rw [sqrt_sq_eq_abs, abs_of_pos] at h
        · have : m = -1 / 2 := by linarith only [h]
          linarith
        · linarith only [hm]
    · simp at h ⊢
      simp [h]
      norm_num
