import Mathlib

/- Show that if $a, b$ and $c$ are positive numbers, then


$$

a^{\frac{3}{4}}+b^{\frac{3}{4}}+c^{\frac{3}{4}}>(a+b+c)^{\frac{3}{4}}

$$
 -/

--First we prove the following lemma: a ^ (-1 / 4 : ℝ) > (a + b + c) ^ (-1 / 4 : ℝ).
lemma help (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ (-1 / 4 : ℝ) > (a + b + c) ^ (-1 / 4 : ℝ) := by
  have : a < a + b + c := by
    have : 0 < b + c := by positivity
    linarith
  refine Real.rpow_lt_rpow_of_exponent_neg ha this ?_
  norm_num


theorem inequalities_218478 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^(3/4) + b^(3/4) + c^(3/4) > (a + b + c)^(3/4) := by

      --Using the lemma we obtain a ^ (-1 / 4 : ℝ) > (a + b + c) ^ (-1 / 4 : ℝ).
      have h1 : a ^ (-1 / 4 : ℝ) > (a + b + c) ^ (-1 / 4 : ℝ) := by
        apply help
        all_goals linarith

      --Using the lemma we obtain b ^ (-1 / 4 : ℝ) > (b + a + c) ^ (-1 / 4 : ℝ).
      have h2' : b ^ (-1 / 4 : ℝ) > (b + a + c) ^ (-1 / 4 : ℝ) := by
        apply help
        all_goals linarith
      have h2 : b ^ (-1 / 4 : ℝ) > (a + b + c) ^ (-1 / 4 : ℝ) := by
        have : (b + a + c) ^ (-1 / 4 : ℝ) = (a + b + c) ^ (-1 / 4 : ℝ) := by ring_nf
        linarith

      --Using the lemma we obtain c ^ (-1 / 4 : ℝ) > (c + b + a) ^ (-1 / 4 : ℝ).
      have h3' : c ^ (-1 / 4 : ℝ) > (c + b + a) ^ (-1 / 4 : ℝ) := by
        apply help
        all_goals linarith
      have h3 : c ^ (-1 / 4 : ℝ) > (a + b + c) ^ (-1 / 4 : ℝ) := by
        have : (c + b + a) ^ (-1 / 4 : ℝ) = (a + b + c) ^ (-1 / 4 : ℝ) := by ring_nf
        linarith

      --But a ^ (3 / 4 : ℝ) + b ^ (3 / 4 : ℝ) + c ^ (3 / 4 : ℝ) = a * a ^ ( -1 / 4 : ℝ) + b * b ^ (-1 / 4 : ℝ) + c * c ^ (-1 / 4 : ℝ).
      have h4 : a ^ (3 / 4 : ℝ) + b ^ (3 / 4 : ℝ) + c ^ (3 / 4 : ℝ) = a * a ^ ( -1 / 4 : ℝ) + b * b ^ (-1 / 4 : ℝ) + c * c ^ (-1 / 4 : ℝ) := by
        have h41 : a * a ^ ( -1 / 4 : ℝ) = a ^ (3 / 4 : ℝ) := by calc
          _ = a ^ (1 : ℝ) * a ^ ( -1 / 4 : ℝ) := by
            refine (mul_left_inj' ?_).mpr ?_
            positivity
            exact Eq.symm (Real.rpow_one a)
          _ = a ^ ((1 : ℝ) + (-1 / 4  : ℝ)) := by exact Eq.symm (Real.rpow_add ha 1 (-1 / 4))
          _ = a ^ (3 / 4 : ℝ) := by norm_num

        --And b * b ^ ( -1 / 4 : ℝ) = b ^ (3 / 4 : ℝ).
        have h42 : b * b ^ ( -1 / 4 : ℝ) = b ^ (3 / 4 : ℝ) := by calc
          _ = b ^ (1 : ℝ) * b ^ ( -1 / 4 : ℝ) := by
            refine (mul_left_inj' ?_).mpr ?_
            positivity
            exact Eq.symm (Real.rpow_one b)
          _ = b ^ ((1 : ℝ) + (-1 / 4  : ℝ)) := by exact Eq.symm (Real.rpow_add hb 1 (-1 / 4))
          _ = b ^ (3 / 4 : ℝ) := by norm_num

        --And c * c ^ ( -1 / 4 : ℝ) = c ^ (3 / 4 : ℝ).
        have h43 : c * c ^ ( -1 / 4 : ℝ) = c ^ (3 / 4 : ℝ) := by calc
          _ = c ^ (1 : ℝ) * c ^ ( -1 / 4 : ℝ) := by
            refine (mul_left_inj' ?_).mpr ?_
            positivity
            exact Eq.symm (Real.rpow_one c)
          _ = c ^ ((1 : ℝ) + (-1 / 4  : ℝ)) := by exact Eq.symm (Real.rpow_add hc 1 (-1 / 4))
          _ = c ^ (3 / 4 : ℝ) := by norm_num

        linarith

      --Moreover, it follows that a * a ^ ( -1 / 4 : ℝ) + b * b ^ (-1 / 4 : ℝ) + c * c ^ (-1 / 4 : ℝ) > a * (a + b + c) ^ (-1 / 4 : ℝ) + b * (a + b + c) ^ (-1 / 4 : ℝ) + c * (a + b + c) ^ (-1 / 4 : ℝ)
      have h5 : a * a ^ ( -1 / 4 : ℝ) + b * b ^ (-1 / 4 : ℝ) + c * c ^ (-1 / 4 : ℝ) > a * (a + b + c) ^ (-1 / 4 : ℝ) + b * (a + b + c) ^ (-1 / 4 : ℝ) + c * (a + b + c) ^ (-1 / 4 : ℝ) := by
        gcongr

      --Show a * (a + b + c) ^ (-1 / 4 : ℝ) + b * (a + b + c) ^ (-1 / 4 : ℝ) + c * (a + b + c) ^ (-1 / 4 : ℝ) = (a + b + c) * (a + b + c) ^ (-1 / 4 : ℝ).
      have h6 : a * (a + b + c) ^ (-1 / 4 : ℝ) + b * (a + b + c) ^ (-1 / 4 : ℝ) + c * (a + b + c) ^ (-1 / 4 : ℝ) = (a + b + c) * (a + b + c) ^ (-1 / 4 : ℝ) := by ring

      --Show (a + b + c) * (a + b + c) ^ (-1 / 4 : ℝ) = (a + b + c) ^ (3 / 4 : ℝ).
      have h7 : (a + b + c) * (a + b + c) ^ (-1 / 4 : ℝ) = (a + b + c) ^ (3 / 4 : ℝ) := by calc
        _ = (a + b + c) ^ (1 : ℝ) * (a + b + c) ^ (-1 / 4 : ℝ) := by
          refine (mul_left_inj' ?_).mpr ?_
          positivity
          exact Eq.symm (Real.rpow_one (a + b + c))
        _ = (a + b + c) ^ ( (1 : ℝ) + (-1 / 4 : ℝ)) := by
          refine Eq.symm (Real.rpow_add' ?_ ?_)
          positivity
          norm_num
        _ = (a + b + c) ^ ( (3 / 4) : ℝ) := by
          norm_num

      --Hence we get the inequality.
      linarith