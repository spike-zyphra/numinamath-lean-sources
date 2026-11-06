import Mathlib

theorem inequalities_244314 (a b c : ℝ) (ha : a = 3.14) (hb : b = 0.67) (hc : c > 0)
    (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : ∃ n : ℤ, c = n) :
    c = 3 := by
  rcases h''' with ⟨n, hn⟩
  rw [ha, hb] at h h' h''
  rw [hn] at h h' h''
  have h1 : (n : ℝ) < 3.81 := by linarith
  have h2 : (n : ℝ) > 2.47 := by linarith
  have h3 : n ≤ 3 := by
    by_contra h4
    push_neg at h4
    have h5 : n ≥ 4 := by omega
    have h6 : (n : ℝ) ≥ (4 : ℝ) := by
      exact_mod_cast h5
    linarith
  have h4 : n ≥ 3 := by
    by_contra h5
    push_neg at h5
    have h6 : n ≤ 2 := by omega
    have h7 : (n : ℝ) ≤ (2 : ℝ) := by
      exact_mod_cast h6
    linarith
  have hn3 : n = 3 := by omega
  have hc3 : c = (3 : ℝ) := by
    rw [hn]
    norm_num [hn3]
  linarith