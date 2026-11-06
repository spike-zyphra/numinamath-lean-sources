import Mathlib

/- Soient $a, b, c, d$ quatre réels tels que $|a|>1,|b|>1,|c|>1$ et $|d|>1$. Supposons que $(a+1)(b+1)(c+1)(d+1)=(a-1)(b-1)(c-1)(d-1)$. Montrer que

$$
\frac{1}{a-1}+\frac{1}{b-1}+\frac{1}{c-1}+\frac{1}{d-1}>0
$$ -/
theorem algebra_607164 {a b c d : ℝ} (ha : |a| > 1) (hb : |b| > 1) (hc : |c| > 1) (hd : |d| > 1)
    (h : (a + 1) * (b + 1) * (c + 1) * (d + 1) = (a - 1) * (b - 1) * (c - 1) * (d - 1)) :
    0 < 1 / (a - 1) + 1 / (b - 1) + 1 / (c - 1) + 1 / (d - 1) := by
        simp at ha hb hc hd

        -- some basic fact needed later
        have : a - 1 ≠ 0 := by
            by_contra aeq1
            have : |a| = 1 := by rw [abs_eq]; left; linarith; linarith
            linarith
        have : b - 1 ≠ 0 := by
            by_contra beq1
            have : |b| = 1 := by rw [abs_eq]; left; linarith; linarith
            linarith
        have : c - 1 ≠ 0 := by
            by_contra ceq1
            have : |c| = 1 := by rw [abs_eq]; left; linarith; linarith
            linarith
        have : d - 1 ≠ 0 := by
            by_contra deq1
            have : |d| = 1 := by rw [abs_eq]; left; linarith; linarith
            linarith

        let x:ℝ := (a+1)/(a-1)
        let y:ℝ := (b+1)/(b-1)
        let z:ℝ := (c+1)/(c-1)
        let w:ℝ := (d+1)/(d-1)

        -- using |a| > 1, we have 0 < x and similarly for others.
        have xnng : 0 ≤  x := by
            have : 1 ≤ |a| := by linarith
            have va: a ≤ -1 ∨ 1 ≤ a := by rw [le_abs'] at this; assumption
            simp [x]
            obtain alem1 | age1 := va
            have : a+1 ≤0 := by linarith
            have : a-1 ≤0 := by linarith
            refine div_nonneg_iff.mpr ?_; tauto
            have : 0≤ a+1 := by linarith
            have : 0≤ a-1 := by linarith
            refine div_nonneg_iff.mpr ?_; tauto
        have ynng : 0 ≤  y := by
            have : 1 ≤ |b| := by linarith
            have vb: b ≤ -1 ∨ 1 ≤ b := by rw [le_abs'] at this; assumption
            simp [y]
            obtain blem1 | bge1 := vb
            have : b+1 ≤0 := by linarith
            have : b-1 ≤0 := by linarith
            refine div_nonneg_iff.mpr ?_; tauto
            have : 0≤ b+1 := by linarith
            have : 0≤  b-1 := by linarith
            refine div_nonneg_iff.mpr ?_; tauto
        have znng : 0 ≤ z := by
            have : 1 ≤ |c| := by linarith
            have vc: c ≤ -1 ∨ 1 ≤ c := by rw [le_abs'] at this; assumption
            simp [z]
            obtain clem1 | cge1 := vc
            have : c+1 ≤0 := by linarith
            have : c-1 ≤0 := by linarith
            refine div_nonneg_iff.mpr ?_; tauto
            have : 0≤ c+1 := by linarith
            have : 0≤ c-1 := by linarith
            refine div_nonneg_iff.mpr ?_; tauto
        have wnng : 0 ≤ w := by
            have : 1 ≤ |d| := by linarith
            have vd: d ≤ -1 ∨ 1 ≤ d := by rw [le_abs'] at this; assumption
            simp [w]
            obtain dlem1 | dge1 := vd
            have : d+1 ≤0 := by linarith
            have : d-1 ≤0 := by linarith
            refine div_nonneg_iff.mpr ?_; tauto
            have : 0≤ d+1 := by linarith
            have : 0≤ d-1 := by linarith
            refine div_nonneg_iff.mpr ?_; tauto

        -- using h, we get xyzw = 1
        have xyzweq1 : x * y * z * w = 1 := by simp [x,y,z,w]; field_simp [h]
        -- use the definition of x,y,z,w
        have oneovereqxyzw:1 / (a - 1) + 1 / (b - 1) + 1 / (c - 1) + 1 / (d - 1) = (x + y + z + w - 4) /2 := by
            have : x = 1 + 2 / (a-1) := by field_simp[x]; ring
            have : 1/(a-1) = (x-1)/2 := by field_simp[x]; ring
            have : y = 1 + 2 / (b-1) := by field_simp[y]; ring
            have : 1/(b-1) = (y-1)/2 := by field_simp[y]; ring
            have : z = 1 + 2 / (c-1) := by field_simp[z]; ring
            have : 1/(c-1) = (z-1)/2 := by field_simp[z]; ring
            have : w = 1 + 2 / (d-1) := by field_simp[w]; ring
            have : 1/(d-1) = (w-1)/2 := by field_simp[w]; ring
            have :(x-1)/2 + (y-1) /2 + (z-1) /2 + (w-1)/2 = (x+y+z+w -4)/2 := by linarith
            linarith

        -- it suffices to prove x + y + z + w > 4, which is a simple application of the AM-GM inequality
        suffices g : 4 < x + y + z + w by rw [oneovereqxyzw]; nlinarith

        let oq:ℝ := (1:ℝ)/(4:ℝ)
        have oqnng : 0 ≤ oq := by positivity
        have sumoq : oq + oq + oq + oq = 1 := by ring_nf;
        have mulpow: (x*y*z*w)^oq = x^oq * y^oq * z ^oq * w^oq := by
            rw [Real.mul_rpow]; rw [Real.mul_rpow]; rw [Real.mul_rpow]
            assumption; assumption; apply mul_nonneg; assumption; assumption; assumption; apply mul_nonneg; apply mul_nonneg; assumption; assumption; assumption; assumption
        have : x^oq * y^oq * z ^oq * w^oq ≤ oq * x + oq * y + oq * z + oq * w := by
            exact Real.geom_mean_le_arith_mean4_weighted oqnng oqnng oqnng oqnng xnng ynng znng wnng sumoq
        have : 1 = (x*y*z*w)^oq := by rw [xyzweq1]; field_simp
        have : 1 ≤ oq * x + oq * y + oq * z + oq * w := by linarith
        have fourle: 4 ≤ x + y + z + w := by field_simp [oq] at this; linarith

        have fourneq: 4 ≠ x + y + z + w := by
            by_contra xpypzpweq4
            have oqxyzweq1 : oq * x + oq * y + oq * z + oq * w = 1 := by simp [oq]; linarith
            have : x = 1 := by
                have gmeqam : x^(oq) * y^(oq) * z^(oq) * w^(oq) = oq * x + oq * y + oq * z + oq * w := by
                  rw [← mul_add]; rw [← mul_add]; rw [← mul_add]; rw [← xpypzpweq4];
                  rw [←mulpow]; rw[xyzweq1]; simp [oq]

                let s : Finset (Fin 4) := {0,1,2,3}
                let d : Fin 4 → ℝ := fun _ => oq
                let u : Fin 4 → ℝ
                | ⟨0, _⟩ => x
                | ⟨1, _⟩ => y
                | ⟨2, _⟩ => z
                | ⟨3, _⟩ => w
                have tmp2 : ∑ i ∈  s, d i * u i = oq * x + oq * y + oq * z + oq * w := by
                    simp [s,d,u,x,y,z,w,oq]; ring_nf
                have myeq : ∏ i ∈  s, u i ^ d i = ∑ i ∈  s, d i * u i := by
                    have tmp1 : ∏ i ∈  s, u i ^ d i = x^(oq) * y^(oq) * z^(oq) * w^(oq) := by
                        simp [s,d,u,x,y,z,w,oq]; field_simp; ring_nf
                    rw [tmp1, tmp2]; exact gmeqam
                rw [Real.geom_mean_eq_arith_mean_weighted_iff'] at myeq
                have u0eq1 : u 0 = 1 := by
                  calc
                    u 0 = ∑ i ∈  s, d i * u i := by apply myeq 0; simp [s]
                    _ = oq * x + oq * y + oq * z + oq * w := by exact tmp2
                    _ = 1 := by exact oqxyzweq1
                simp [u] at u0eq1; assumption;
                intro i hi; simp [d, oq, s];
                simp [s,d,oq]; intro i hi; simp[u]; bound
            have xneq1 : x ≠ 1 := by
                by_contra xeq1; field_simp [x] at xeq1
                have : (a+1)/(a-1) * (a-1) = (a-1) := by rw [xeq1]; simp
                have : (a+1)/(a-1) * (a-1) = (a+1) := by field_simp
                have : a + 1 = a - 1 := by congr
                linarith
            contradiction
        exact lt_of_le_of_ne fourle fourneq
