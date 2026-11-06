import Mathlib

open BigOperators
/- Let $a, b, c$ be positive real numbers such that $a b c=8$. Prove that

$$
\frac{a b+4}{a+2}+\frac{b c+4}{b+2}+\frac{c a+4}{c+2} \geq 6
$$ -/
theorem inequalities_605144 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 8) :
    6 ≤ (a * b + 4) / (a + 2) + (b * c + 4) / (b + 2) + (c * a + 4) / (c + 2) := by{
      -- First, we simplify the left.
    have keya : (a*b+4) = 4*(c+2)/c :=by{
      field_simp
      rw [add_mul, habc]
      ring
    }
    have keyb : (b*c+4) = 4*(a+2)/a :=by{
      field_simp
      rw [add_mul]
      have hbca: b*c*a=8:=by{
        rw [mul_comm, ← mul_assoc, habc]
      }
      rw [hbca]
      ring
    }
    have keyc : (c*a+4) = 4*(b+2)/b :=by{
      field_simp
      rw [add_mul]
      have hcab: c*a*b=8:=by{
        rw [mul_assoc, mul_comm, habc]
      }
      rw [hcab]
      ring
    }
    -- We have the mul-equation.
    have key : (a*b+4)/(a+2) * (b*c+4)/(b+2) * (c*a+4)/(c+2) = 8:=by{
      rw [keya, keyb, keyc]
      field_simp
      calc
        4 * (c + 2) * (4 * (a + 2)) * (4 * (b + 2)) = 64 * (a+2) * (b+2) * (c+2) :=by ring
        _ = 8 *(a*b*c) * (a+2) * (b+2) * (c+2) :=by{
          rw [habc]
          ring
        }
        _ = 8 * (c * (a + 2) * a * (b + 2) * b * (c + 2)) :=by ring
    }
    -- Then we use the AMGM inequality.
    -- wi is the weight.
    let w1:= (1:ℝ)/3
    let w2:= (1:ℝ)/3
    let w3:= (1:ℝ)/3
    have hw1:0≤ w1:=by positivity
    have hw2:0≤ w2:=by positivity
    have hw3:0≤ w3:=by positivity
    have hp1:0≤ (a * b + 4) / (a + 2):=by positivity
    have hp2:0≤ (b * c + 4) / (b + 2):=by positivity
    have hp3:0≤ (c * a + 4) / (c + 2):=by positivity
    have hw:w1+w2+w3=1:=by{
      norm_num
    }
    let h := Real.geom_mean_le_arith_mean3_weighted hw1 hw2 hw3 hp1 hp2 hp3 hw
    -- Simplify the right of h using key
    have key2 : ((a * b + 4) / (a + 2)) ^ w1 * ((b * c + 4) / (b + 2)) ^ w2 * ((c * a + 4) / (c + 2)) ^ w3 = 2:=by{
      calc
       ((a * b + 4) / (a + 2)) ^ w1 * ((b * c + 4) / (b + 2)) ^ w2 * ((c * a + 4) / (c + 2)) ^ w3
        = ((a*b+4)/(a+2) * (b*c+4)/(b+2) * (c*a+4)/(c+2)) ^ ((1:ℝ)/3):=by {
          field_simp [w1, w2, w3]
          rw [← Real.mul_rpow, ← Real.mul_rpow]
          field_simp
          positivity
          positivity
          positivity
          positivity
          }
      _ = 2:=by{
          rw [key]
          have h8 : (8 : ℝ) = 2^3 := by norm_num
          rw [h8]
          rw [← Real.rpow_natCast_mul]
          field_simp
          positivity
          }
    }
    rw [key2] at h
    -- Finally we use h to solve the problem.
    calc
      (a * b + 4) / (a + 2) + (b * c + 4) / (b + 2) + (c * a + 4) / (c + 2)
        = 3 * (w1 * ((a * b + 4) / (a + 2)) + w2 * ((b * c + 4) / (b + 2)) + w3 * ((c * a + 4) / (c + 2))):=by ring
      _ ≥ 3 * 2:=by{
        apply mul_le_mul
        simp
        exact h
        positivity
        positivity
      }
      _ = 6:=by norm_num
    }