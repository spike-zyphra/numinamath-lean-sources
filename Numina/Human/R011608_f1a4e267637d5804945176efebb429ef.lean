import Mathlib

open Real

/-The solution to the system of equations
x=elny,
y=elnz,
z=elnx
is ?
-/

theorem algebra_294075: {(x, y, z): ℝ × ℝ × ℝ | 0 < x ∧ 0 < y ∧ 0 < z ∧
x = exp 1 * log y ∧ y = exp 1 * log z ∧ z = exp 1 * log x} = {(exp 1, exp 1, exp 1)} := by
  ext ⟨x, y, z⟩

  -- show a basic result
  have o: 0 < exp 1 := by
    apply Real.exp_pos

  constructor
  -- the forward direction
  .
    intro h
    simp at h
    rcases h with ⟨lx, ly, lz, hx, hy, hz⟩
    simp

    -- we show x ≤ y
    have rxy: x ≤ y := by
      by_contra! r
      -- show x < z
      have r1: x < z := by
        rw [hx, hz]
        have s: log y < log x := by
          apply Real.log_lt_log
          linarith
          exact r
        nlinarith
      -- show z < y
      have r2: z < y := by
        rw [hz, hy]
        have s: log x < log z := by
          apply Real.log_lt_log
          linarith
          exact r1
        nlinarith
      -- now x < z < y < x, contradiction
      nlinarith

    -- we show y ≤ x
    have ryx: y ≤ x := by
      by_contra! r
      -- show y < z
      have r1: z < x := by
        rw [hx, hz]
        have s: log x < log y := by
          apply Real.log_lt_log
          linarith
          exact r
        nlinarith
      -- show y < z
      have r2: y < z := by
        rw [hz, hy]
        have s: log z < log x := by
          apply Real.log_lt_log
          linarith
          exact r1
        nlinarith
      -- now x < y < z < x, contradiction
      nlinarith

    -- hence x = y
    have s1: x = y := by nlinarith
    simp [s1] at *

    -- show y ≤ z
    have ryz: y ≤ z := by
      by_contra! r
      have r1: y < z := by
        rw [hy]
        nth_rewrite 2 [hz]
        have s: log z < log y := by
          apply Real.log_lt_log
          linarith
          exact r
        nlinarith
      nlinarith

    -- show z ≤ y
    have rzy: z ≤ y := by
      by_contra! r
      have r1: z < y := by
        rw [hz]
        nth_rewrite 2 [hy]
        have s: log y < log z := by
          apply Real.log_lt_log
          linarith
          exact r
        nlinarith
      nlinarith

    have s2: y = z := by nlinarith
    simp [s2] at *
    clear ryz rzy s2 hy hx lx ly rxy ryx s1

    -- finally, we show z = e
    set u:= z / exp 1
    replace hz: u = log z := by
      simp [u]
      field_simp
      linarith
    replace hz: exp (u) = z := by
      rw [hz]
      apply Real.exp_log
      linarith
    have hu: z = u * exp 1 := by simp [u]
    rw [hu] at hz lz
    rw [hu]
    have lu: 0 < u := by nlinarith
    clear hu lz
    clear_value u
    have vu: u = 1 := by
      by_contra! v
      have c:= Real.log_lt_sub_one_of_pos  lu v -- use the inequality log u < u - 1
      replace hz: exp (u - 1) = u := by
        rw [Real.exp_sub]
        rw [hz]
        field_simp
      replace hz: log (exp (u - 1)) = log u := by
        rw [hz]
      have s1: log (exp (u - 1)) = u - 1 := by
        apply Real.log_exp
      rw [s1] at hz
      clear s1
      simp [hz] at c

    simp [vu]


  -- the backward direction
  .
    intro h
    simp at h
    simp [h]
    exact o
    