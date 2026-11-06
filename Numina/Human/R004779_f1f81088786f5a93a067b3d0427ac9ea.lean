import Mathlib

open Real

set_option maxHeartbeats 500000

theorem algebra_322593 (k : ℝ):
 (∃! x, x ≠ -2 ∧ x ≠ 0 ∧ (2 * k / (x + 2) - (x - 1) / (x ^ 2 + 2 * x) = (k * x + 1) / x))
  ↔ k = 3 / 4 ∨ k = 0 ∨ k = 1 := by


  constructor
  . intro hx
    rcases hx with ⟨x, ⟨⟨hx1, hx2, hx3⟩, hy⟩⟩

    rw [(by linarith : (x ^ 2 + 2 * x) = x * (x + 2))] at hx3

    field_simp at hx3
    rw [sub_mul] at hx3

    have : (x - 1) / (x * (x + 2)) * x = (x - 1) / (x + 2) := by
      have : x+2 ≠ 0 := by contrapose! hx1; linarith
      field_simp
      ring_nf
    rw [this] at hx3

    have : x+2 ≠ 0 := by contrapose! hx1; linarith
    field_simp at hx3

    by_contra hk
    simp at hk
    have ⟨hk1, hk2, hk3⟩ := hk

    by_cases hk4: k > 1
    . have : k*x^2=-2*x-1:= by linarith

      have h1: k*(x+1/k)^2=1/k-1:= by
        ring_nf
        field_simp
        rw [this]
        linarith

      have : k*(x+1/k)^2 ≥ 0:= by positivity
      rw [h1] at this
      -- have : 1/k ≥ 1:= by linarith

      have : 1/k < 1 := by
        apply (div_lt_iff₀ (by linarith)).mpr
        linarith
      linarith


    . simp at hk4
      have hk5 : k < 1 := lt_of_le_of_ne hk4 hk3
      let x1 := (-1-sqrt (1-k))/k
      let x2 := (-1+sqrt (1-k))/k
      have h_x1_1 : x1 ≠ -2 := by
        by_contra h_contra
        unfold x1 at h_contra
        field_simp at h_contra
        have : √(1 - k) = 2*k-1 := by linarith

        by_cases hk6: 0 ≤ 2 * k - 1
        . rw [sqrt_eq_iff_eq_sq (by linarith) hk6] at this
          have : k*(4*k-3)=0 := by linarith
          simp at this
          rcases this with h | h
          . tauto
          . have : k = 3/4 := by linarith
            tauto
        . simp at hk6
          have : √(1 - k) ≥ 0 := by positivity
          linarith

      have h_x1_2 : x1 ≠ 0 := by
        by_contra h_contra
        unfold x1 at h_contra
        field_simp at h_contra
        have : √(1 - k) ≥ 0 := by positivity
        linarith

      have h_x1_3 : 2 * k / (x1 + 2) - (x1 - 1) / (x1 ^ 2 + 2 * x1) = (k * x1 + 1) / x1 := by
        field_simp
        rw [sub_mul]
        have : (x1 - 1) / (x1 ^ 2 + 2 * x1) * x1 = (x1 - 1) / (x1 + 2) := by
          have : x1+2 ≠ 0 := by contrapose! h_x1_1; linarith
          rw [(by ring : x1 ^ 2 + 2 * x1 = (x1 + 2) * x1)]
          field_simp
          ring_nf

        rw [this]
        have : x1+2 ≠ 0 := by contrapose! h_x1_1; linarith
        field_simp
        unfold x1
        ring_nf
        field_simp
        rw [sq_sqrt (by linarith)]
        ring_nf

      have h_x2_1 : x2 ≠ -2 := by
        by_contra h_contra
        unfold x2 at h_contra
        field_simp at h_contra
        have : √(1 - k) = 1 - 2*k := by linarith
        by_cases hk6: 0 ≤ 1 - 2*k
        . rw [sqrt_eq_iff_eq_sq (by linarith) hk6] at this
          have : k*(4*k-3)=0 := by linarith
          simp at this
          rcases this with h | h
          . tauto
          . have : k = 3/4 := by linarith
            tauto
        . simp at hk6
          have : √(1 - k) ≥ 0 := by positivity
          linarith

      have h_x2_2 : x2 ≠ 0 := by
        by_contra h_contra
        unfold x2 at h_contra
        field_simp at h_contra
        have : √(1 - k) = 1 := by linarith
        rw [sqrt_eq_iff_eq_sq (by linarith) (by linarith)] at this
        have : k = 0 := by linarith
        subst k
        tauto

      have h_x2_3 : 2 * k / (x2 + 2) - (x2 - 1) / (x2 ^ 2 + 2 * x2) = (k * x2 + 1) / x2 := by
        field_simp
        rw [sub_mul]
        have : (x2 - 1) / (x2 ^ 2 + 2 * x2) * x2 = (x2 - 1) / (x2 + 2) := by
          have : x2+2 ≠ 0 := by contrapose! h_x2_1; linarith
          rw [(by ring : x2 ^ 2 + 2 * x2 = (x2 + 2) * x2)]
          field_simp
          ring_nf
        rw [this]
        have : x2+2 ≠ 0 := by contrapose! h_x2_1; linarith
        field_simp
        unfold x2
        ring_nf
        field_simp
        rw [sq_sqrt (by linarith)]
        ring_nf

      have hy1 := hy x1
      have hy2 := hy x2

      simp at hy1 hy2

      have hy1 := hy1 h_x1_1 h_x1_2 h_x1_3
      have hy2 := hy2 h_x2_1 h_x2_2 h_x2_3

      rw [← hy2] at hy1
      unfold x1 x2 at hy1
      field_simp at hy1

      have : √(1 - k) = 0 := by linarith
      rw [sqrt_eq_zero (by linarith)] at this
      have : k = 1 := by linarith
      subst k
      tauto


  . intro hk
    rcases hk with rfl | rfl | rfl
    . use -(2/3)
      simp
      norm_num
      intro x hx1 hx2 hx3
      rw [(by linarith : (x ^ 2 + 2 * x) = x * (x + 2))] at hx3
      field_simp at hx3
      rw [sub_mul] at hx3
      have : (x - 1) / (x * (x + 2)) * (4 * x) = 4 * (x - 1) / (x + 2) := by
        have : x+2 ≠ 0 := by contrapose! hx1; linarith
        field_simp
        ring_nf
      rw [this] at hx3

      have : 3 / (2 * (x + 2)) * (4 * x)  = 6 * x / (x + 2) := by
        have : x+2 ≠ 0 := by contrapose! hx1; linarith
        field_simp
        ring_nf
      rw [this] at hx3
      have : x+2 ≠ 0 := by contrapose! hx1; linarith
      field_simp at hx3
      have : (x+2)*(3*x+2)=0 := by linarith
      simp at this
      rcases this with h | h
      . tauto
      . linarith

    . use -(1/2)
      simp
      norm_num
      intro x hx1 hx2 hx3
      rw [(by linarith : (x ^ 2 + 2 * x) = x * (x + 2))] at hx3
      have : x+2 ≠ 0 := by contrapose! hx1; linarith
      field_simp at hx3
      have : x*(2*x+1)=0 := by linarith
      simp at this
      rcases this with rfl | h
      . tauto
      . linarith

    . use -1
      simp
      norm_num
      intro x hx1 hx2 hx3

      rw [(by linarith : (x ^ 2 + 2 * x) = x * (x + 2))] at hx3
      --
      field_simp at hx3
      rw [sub_mul] at hx3
      have: (x - 1) / (x * (x + 2)) * x = (x - 1) / (x + 2) := by
        have : x+2 ≠ 0 := by contrapose! hx1; linarith
        field_simp
        ring_nf
      rw [this] at hx3
      have : x+2 ≠ 0 := by contrapose! hx1; linarith
      field_simp at hx3
      have : (x+1)^2 = 0 := by linarith
      simp at this
      linarith
