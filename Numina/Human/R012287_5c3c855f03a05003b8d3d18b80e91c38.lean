import Mathlib
open Real
/- if b>1 sin x>0, cos x>0, and log_b(sin x)=a, then log_b(cos x) equals:
(A) 2log_b(1-b^(a/2)) (B) √(1-a^2) (C) b^(a^2) (D) (1/2)log_b(1-b^(2a)) (E) none of these -/
theorem algebra_93692 (b x a : ℝ)
  (hb : b > 1)
  (hsin : sin x > 0)
  (hcos : cos x > 0)
  (ha : logb b (sin x) = a) : logb b (cos x) = 1 / 2 * logb b (1 - b ^ (2 * a)) := by
  -- obtaining b^a=sin x, b^c=cos x
  have adef:=ha
  rw [logb_eq_iff_rpow_eq] at ha <;> try linarith
  set c:=logb b (cos x) with ← hc
  rw [logb_eq_iff_rpow_eq] at hc <;> try linarith
  -- substituting into sin^2 x + cos^2 x = 1
  have h:=sin_sq_add_cos_sq x
  rw [← ha,← hc] at h
  rw [← rpow_natCast,← rpow_mul (by linarith:0≤b) a (2:ℕ)] at h
  rw [← rpow_natCast,← rpow_mul (by linarith:0≤b) c (2:ℕ)] at h
  norm_cast at h
  -- obtaining b^(2c)=1-b^(2a)
  have h': b ^ (c * 2) = 1 - b ^ (a * 2) := by linarith
  field_simp;symm
  -- then we can obtain the result but we still need to prove b ^ (2 * a) < 1
  rw [logb_eq_iff_rpow_eq,mul_comm 2 a] <;> try linarith
  have h1:b ^ (2 * a) < 1:= by
    -- equivalently we need to prove a<0, that is log_b(sin x)<0
    rw [rpow_lt_one_iff_of_pos (by linarith)]
    left;simp [hb];rw [mul_neg_iff];left;simp
    -- that is, sin x < 1
    rw [← adef,logb_neg_iff]<;> try linarith
    -- since sin x ≤ 1 we need to prove sin x ≠ 1
    apply Ne.lt_of_le
    · intro hsineq1
      -- sin x ≠ 1, because if sin x=1 then cos x=0 which contradict a hypothesis 
      have h2:=sin_sq_add_cos_sq x
      rw [hsineq1,pow_two,pow_two] at h2
      have h2':cos x * cos x =0:=by linarith
      simp at h2';linarith
    · exact sin_le_one x
  nlinarith