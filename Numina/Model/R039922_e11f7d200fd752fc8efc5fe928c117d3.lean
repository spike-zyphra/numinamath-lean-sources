import Mathlib

theorem algebra_246684 {n m : ℕ} (hn : n = m + 2) (hmn : m > 0 ∧ n > 0) :
  let a5 := (15 / 100 : ℝ) * n     -- A班5分学生人数
  let a4 := 2 * a5 + 4             -- A班4分学生人数
  let a3 := (1 / 4 : ℝ) * n        -- A班3分学生人数
  let a2 := (1 / 5 : ℝ) * n        -- A班2分学生人数
  
  let b5 := a5 - 1                 -- B班5分学生人数
  let b4 := (1 / 2 : ℝ) * m - 4    -- B班4分学生人数
  let b_rest := m - b5 - b4        -- B班剩余学生人数
  let b3 := (5 / 6 : ℝ) * b_rest   -- B班3分学生人数
  let b2 := (1 / 6 : ℝ) * b_rest   -- B班2分学生人数
  
  let A_avg := (5 * a5 + 4 * a4 + 3 * a3 + 2 * a2) / n  -- A班平均分
  let B_avg := (5 * b5 + 4 * b4 + 3 * b3 + 2 * b2) / m  -- B班平均分
  
  (a5 + a4 + a3 + a2 = n) →        -- A班学生总数约束
  (b5 + b4 + b3 + b2 = m) →        -- B班学生总数约束
  (B_avg > A_avg)                  -- B班平均分更高
  := by 
  rcases hmn with ⟨hm, hn_pos⟩
  intro a5 a4 a3 a2 b5 b4 b_rest b3 b2 A_avg B_avg h1 h2
  have hn_eq : (n : ℝ) = (40 : ℝ) := by
    have h1' := h1
    simp [a5, a4, a3, a2] at h1'
    have hn' : (n : ℝ) = (40 : ℝ) := by
      linarith 
    exact_mod_cast hn'
  have hm_eq : (m : ℝ) = (38 : ℝ) := by
    have hn' : (n : ℝ) = (40 : ℝ) := hn_eq
    have h_eq : (n : ℝ) = (m : ℝ) + (2 : ℝ) := by
      exact_mod_cast hn
    linarith 
  have ha5 : (a5 : ℝ) = (6 : ℝ) := by
    simp [a5, hn_eq]
    <;> linarith
  have ha4 : (a4 : ℝ) = (16 : ℝ) := by
    simp [a4, ha5]
    <;> linarith
  have ha3 : (a3 : ℝ) = (10 : ℝ) := by 
    simp [a3, hn_eq]
    <;> linarith
  have ha2 : (a2 : ℝ) = (8 : ℝ) := by
    simp [a2, hn_eq]
    <;> linarith
  have hb5 : (b5 : ℝ) = (5 : ℝ) := by
    simp [b5, ha5]
    <;> linarith
  have hb4 : (b4 : ℝ) = (15 : ℝ) := by
    simp [b4, hm_eq]
    <;> linarith
  have hb_rest : (b_rest : ℝ) = (18 : ℝ) := by 
    simp [b_rest, hb5, hb4, hm_eq]
    <;> linarith
  have hb3 : (b3 : ℝ) = (15 : ℝ) := by 
    simp [b3, hb_rest]
    <;> linarith
  have hb2 : (b2 : ℝ) = (3 : ℝ) := by 
    simp [b2, hb_rest]
    <;> linarith
  have hA_avg : (A_avg : ℝ) = (3.5 : ℝ) := by 
    simp [A_avg, ha5, ha4, ha3, ha2, hn_eq]
    <;> norm_num
  have hB_avg : (B_avg : ℝ) = (136 / 38 : ℝ) := by 
    simp [B_avg, hb5, hb4, hb3, hb2, hm_eq]
    <;> norm_num
  rw [hA_avg, hB_avg]
  norm_num