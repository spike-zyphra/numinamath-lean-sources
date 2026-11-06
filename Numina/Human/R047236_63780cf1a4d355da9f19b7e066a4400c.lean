import Mathlib

/- 5. 1. 15 * Given: $\frac{\cos x+\cos y+\cos z}{\cos (x+y+z)}=\frac{\sin x+\sin y+\sin z}{\sin (x+y+z)}=a$.

Prove: $\cos (y+z)+\cos (z+x)+\cos (x+y)=a$.

 -/
theorem algebra_226855 {x y z a : ℝ} (ha': Real.cos (x + y + z) ≠ 0) (hb': Real.sin (x + y + z) ≠ 0) (ha : (Real.cos x + Real.cos y + Real.cos z) / Real.cos (x + y + z) = a)
    (hb : (Real.sin x + Real.sin y + Real.sin z) / Real.sin (x + y + z) = a) :
    Real.cos (y + z) + Real.cos (z + x) + Real.cos (x + y) = a := by
  -- first convert the problem to complex sin and cos as that is easier to work with
  have ha' : Complex.cos ↑(x + y + z) ≠ 0 := by rw [← Complex.ofReal_cos]; norm_cast
  have hb' : Complex.sin ↑(x + y + z) ≠ 0 := by rw [← Complex.ofReal_sin]; norm_cast
  push_cast at ha'; push_cast at hb'
  have ha : (Complex.cos x + Complex.cos y + Complex.cos z) / Complex.cos (x + y + z) = a := by rw [← Complex.ofReal_cos]; norm_cast
  have hb : (Complex.sin x + Complex.sin y + Complex.sin z) / Complex.sin (x + y + z) = a := by rw [← Complex.ofReal_sin]; norm_cast
  suffices Complex.cos ↑(y + z) + Complex.cos ↑(z + x) + Complex.cos ↑(x + y) = a by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_cos, ← Complex.ofReal_cos] at this;
    norm_cast at this

  -- express the divisions as multiplication
  have ha: (Complex.cos x + Complex.cos y + Complex.cos z) = a * Complex.cos (x + y + z) := by rw  [(eq_mul_inv_iff_mul_eq₀ ha').mp ha.symm]
  have hb: (Complex.sin x + Complex.sin y + Complex.sin z) = a * Complex.sin (x + y + z) := by rw  [(eq_mul_inv_iff_mul_eq₀ hb').mp hb.symm]

  -- use complex variables for ease of work
  push_cast
  set p := (x:ℂ)
  set q := (y:ℂ)
  set r := (z:ℂ)
  set a := (a:ℂ)

  -- unfold the definitions of cos, sin to exponential and cancel out the multiplied I
  dsimp [Complex.cos, Complex.sin] at *
  have hb : (Complex.exp (-p * Complex.I) - Complex.exp (p * Complex.I))  / 2 +
      (Complex.exp (-q * Complex.I) - Complex.exp (q * Complex.I))  / 2 +
    (Complex.exp (-r * Complex.I) - Complex.exp (r * Complex.I))  / 2 =
  a * ((Complex.exp (-(p + q + r) * Complex.I) - Complex.exp ((p + q + r) * Complex.I)) / 2) :=  by
    convert congrArg (fun x => x / Complex.I) hb using 1
    repeat
      field_simp
      ring_nf

  clear * - ha hb

  -- separate hypothesis to positive exponents and negative exponents
  have h₁ : Complex.exp (p * Complex.I) + Complex.exp (q * Complex.I) + Complex.exp (r * Complex.I) = a * Complex.exp ((p+q+r) * Complex.I) := by
     linear_combination ha - hb

  have h₂ : Complex.exp (-p * Complex.I) + Complex.exp (-q * Complex.I) + Complex.exp (-r * Complex.I) = a * Complex.exp (-(p+q+r) * Complex.I) := by
     linear_combination ha + hb

  clear ha hb
  -- express x+y as (x+y+z) - z
  have aux₁ (x y z: ℂ) : Complex.exp ((x + y) * Complex.I) =  Complex.exp ((x + y + z) * Complex.I) * Complex.exp (-z*Complex.I) := by rw [← Complex.exp_add]; ring_nf
  have aux₂ (x y z: ℂ) : Complex.exp (-(x + y) * Complex.I) =  Complex.exp (-(x + y + z) * Complex.I) * Complex.exp (z*Complex.I) := by rw [← Complex.exp_add]; ring_nf

  rw [aux₁ q r p, aux₂ q r p]
  rw [aux₁ r p q, aux₂ r p q]
  rw [aux₁ p q r, aux₂ p q r]

  -- now use the hypothesis to convert the lhs to exp((p+q+r)i) * exp(-(p+q+r)i) * a which proves goal easily
  calc
     (Complex.exp ((q + r + p) * Complex.I) * Complex.exp (-p * Complex.I) +
          Complex.exp (-(q + r + p) * Complex.I) * Complex.exp (p * Complex.I)) /
        2 +
      (Complex.exp ((r + p + q) * Complex.I) * Complex.exp (-q * Complex.I) +
          Complex.exp (-(r + p + q) * Complex.I) * Complex.exp (q * Complex.I)) /
        2 +
    (Complex.exp ((p + q + r) * Complex.I) * Complex.exp (-r * Complex.I) +
        Complex.exp (-(p + q + r) * Complex.I) * Complex.exp (r * Complex.I)) /
      2 = (
        Complex.exp ((p+q+r) * Complex.I) * (Complex.exp (-p * Complex.I) + Complex.exp (-q * Complex.I) + Complex.exp (-r * Complex.I)) +
        Complex.exp (-(p+q+r) * Complex.I) * (Complex.exp (p * Complex.I) + Complex.exp (q * Complex.I) + Complex.exp (r * Complex.I))
      ) / 2 := by ring_nf
    _ = Complex.exp ((p+q+r) * Complex.I) * Complex.exp (-(p+q+r) * Complex.I) * a := by
      rw [h₁, h₂]
      ring
    _ =  a := by rw [← Complex.exp_add]; ring_nf; simp