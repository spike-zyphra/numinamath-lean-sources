import Mathlib

/- 39. The little trains on多多Island are busily working. Thomas and Percy travel from the shed to the harbor, while Edward travels from the harbor to the station. They all immediately return to their starting points after reaching their destinations, completing one round trip before finishing their work. The three trains start at the same time. When Edward arrives at the station, Thomas also happens to be passing the station, while Percy has only traveled $45 \mathrm{~km}$; when Edward returns to the harbor, Thomas is passing the station again. At this point, Thomas's steam engine malfunctions, and he continues at half speed, meeting Percy face-to-face at the midpoint of the line between the shed and the harbor. What is the length of the railway line between the shed and the harbor in $\mathrm{km}$? -/

/-	a &= \text{distance from shed to station} \\
		b &= \text{distance from station to harbor} \\
		L &= a + b = \text{total distance from shed to harbor}\\
		v_t &= \text{Thomas's speed} \\
		v_e &= \text{Edward's speed} \\
		v_p &= \text{Percy's speed} -/
theorem algebra_160505 (a b vₜ vₑ vₚ : ℝ) :
    (a > 0 ∧ b > 0 ∧ vₜ > 0 ∧ vₑ > 0 ∧ vₚ > 0) →
    let L := a + b
    let E₂_vₜ := vₜ/2 -- thomas' speed after event 2
    let ΔDₚ₁ := 45 -- distance percy travels by event 1
    let E_eq (Δt Δd v : ℝ) : Prop := (Δd > 0) → (v > 0) → Δt = Δd/v
    (∃ ΔDₚ₂ : ℝ, -- distance percy travels between event 1 and 2
     let (E₁_dₜ, (E₁_dₑ, E₁_dₚ)) := (a,   b, ΔDₚ₁)
     let (E₂_dₜ, (E₂_dₑ, E₂_dₚ)) := (b+b, b, ΔDₚ₂)
     let (E₃_dₜ,         E₃_dₚ)  := (a - L/2, L/2 - ΔDₚ₂ - ΔDₚ₁)
     -- at event 2, percy has not reached `L/2`
     -- and thomas is at `a` and heading to `L/2`
     (0 < ΔDₚ₂ ∧ ΔDₚ₁+ΔDₚ₂ < L/2 ∧ L/2 < a) ∧
     -- Event 1: Edward arrives at the station.
     (∃ Δt : ℝ, (E_eq Δt E₁_dₜ vₜ) ∧ (E_eq Δt E₁_dₑ vₑ) ∧ (E_eq Δt E₁_dₚ vₚ)) ∧
     -- Event 2: Edward returns to the harbor.
     (∃ Δt : ℝ, (E_eq Δt (E₁_dₜ + E₂_dₜ) vₜ) ∧ (E_eq Δt (E₁_dₑ + E₂_dₑ) vₑ) ∧ (E_eq Δt (E₁_dₚ + E₂_dₚ) vₚ)) ∧
     -- At Event 3, they meet at midpoint $\frac{L}{2}$
     -- event 3 is not viewed as cumulative with respect to previous ones
     (∃ Δt : ℝ, (E_eq Δt E₃_dₜ E₂_vₜ) ∧ (E_eq Δt E₃_dₚ vₚ)))
    → L = 225 := by
  rintro ⟨a_pos, b_pos, vₜ_pos, vₑ_pos, vₚ_pos⟩ L E₂_vₜ ΔDₚ₁ E_eq
  rintro ⟨ΔDₚ₂, ⟨⟨ΔDₚ₂_pos, p_prog_at_ev3, t_prog_at_ev3⟩,
                 ev₁, ev₂, ev₃⟩⟩

  -- Event 1: Edward arrives at the station.
  have ev1_eqs : b/vₑ = a/vₜ ∧ b/vₑ = ΔDₚ₁/vₚ := by
    obtain ⟨Δt, ⟨f₁,f₂,f₃⟩⟩ := ev₁
    have ev1_t := f₁ a_pos vₜ_pos
    have ev1_e := f₂ b_pos vₑ_pos
    have ev1_p := f₃ (by simp [ΔDₚ₁]) vₚ_pos
    constructor
    . rw [← ev1_e, ← ev1_t]
    . rw [← ev1_e, ← ev1_p]

  -- Event 2: Edward returns to the harbor.
  have ev2_eqs : 2*b/vₑ = (a+2*b)/vₜ ∧ 2*b/vₑ = (ΔDₚ₁ + ΔDₚ₂)/vₚ := by
    obtain ⟨Δt, ⟨f₁,f₂,f₃⟩⟩ := ev₂
    have ev2_t := f₁ (by linarith) vₜ_pos
    have ev2_e := f₂ (by linarith) vₑ_pos
    have ev2_p := f₃ (by simp [ΔDₚ₁]; linarith) vₚ_pos
    have : b + b = 2*b := by ring
    rw [← this]
    constructor
    . rw [← ev2_e, ← ev2_t]
    . rw [← ev2_e, ← ev2_p]

  -- \text{Distance traveled by Percy} &= \frac{2b}{v_e} v_p = 2 \frac{45 \text{ km}}{v_p} v_p = 2 \cdot 45 \text{ km} = 90 \text{ km}
  have Dp_at_2 : ΔDₚ₂ = 45 := by
    have eq := by
      calc
        ΔDₚ₁ + ΔDₚ₂
        _ = ((ΔDₚ₁ + ΔDₚ₂)/vₚ)*vₚ := by
            exact Eq.symm (div_mul_cancel₀ _ (Ne.symm (ne_of_lt vₚ_pos)))
        _ = ((2*b)/vₑ)*vₚ := by rw [ev2_eqs.2]
        _ = (2*(b/vₑ))*vₚ := by ring_nf
        _ = (2*(ΔDₚ₁/vₚ))*vₚ := by rw [ev1_eqs.2]
        _ = 2*ΔDₚ₁ := by field_simp
        _ = 90 := by simp [ΔDₚ₁]; norm_num
    calc
      ΔDₚ₂
      _ = (-ΔDₚ₁ + ΔDₚ₁) + ΔDₚ₂ := by ring_nf
      _ = -ΔDₚ₁ + (ΔDₚ₁ + ΔDₚ₂) := by ring_nf
      _ = -ΔDₚ₁ + 90 := by rw [eq]
      _ = 45 := by simp [ΔDₚ₁]; norm_num

  /- From Event 1:
	\begin{align}
		\frac{b}{v_e} &= \frac{a}{v_t} \\
		\Rightarrow v_t &= \frac{a \cdot v_e}{b}
	\end{align} -/
  have vₜ_eq1 : vₜ = (a*vₑ)/b := by
    have equiv := by
      calc
        b/vₑ = a/vₜ
        _ ↔ vₜ*(b/vₑ) = vₜ*(a/vₜ) := by exact Iff.symm (mul_left_cancel_iff_of_pos vₜ_pos)
        _ ↔ vₜ*(b/vₑ) = a := by field_simp
        _ ↔ vₑ*(vₜ*(b/vₑ)) = vₑ*a := by exact Iff.symm (mul_left_cancel_iff_of_pos vₑ_pos)
        _ ↔ vₜ*b = vₑ*a := by field_simp
        _ ↔ (vₜ*b)/b = (vₑ*a)/b := by refine Iff.symm (div_left_inj' (Ne.symm (ne_of_lt b_pos)))
        _ ↔ vₜ = (vₑ*a)/b := by field_simp
        _ ↔ vₜ = (a*vₑ)/b := by ring_nf
    apply equiv.mp ev1_eqs.1

  /- From Event 2:
	\begin{align}
		\frac{2b}{v_e} &= \frac{a + 2b}{v_t} \\
	\end{align}
	Substituting $v_t$ from above:
	\begin{align}
		\frac{2b}{v_e} &= \frac{a + 2b}{\frac{a \cdot v_e}{b}} \\
    ...
		a &= 2b
	\end{align}
	Therefore, the station is twice as far from the shed as it is from the harbor. -/
  have a_from_b : a = 2*b := by
    have equiv := by
      calc
        (2*b)/vₑ = (a + 2*b)/vₜ
        _ ↔ (2*b)/vₑ = (a + 2*b) / ((a*vₑ)/b) := by rw [vₜ_eq1]
        _ ↔ (2*b)/vₑ = (a + 2*b)*b / (a*vₑ) := by field_simp
        _ ↔ (2*b)/vₑ = ((a + 2*b)*b / a)/vₑ := by field_simp
        _ ↔ 2*b = (a + 2*b)*b / a := by refine div_left_inj' (Ne.symm (ne_of_lt vₑ_pos))
        _ ↔ (2*b)*a = ((a + 2*b)*b / a)*a := by exact Iff.symm (mul_right_cancel_iff_of_pos a_pos)
        _ ↔ (2*b)*a = (a + 2*b)*b := by field_simp
        _ ↔ (2*a)*b = (a + 2*b)*b := by ring_nf
        _ ↔ 2*a = a + 2*b := by exact mul_right_cancel_iff_of_pos b_pos
        _ ↔ 2*a - a = a + 2*b - a := by exact Iff.symm sub_left_inj
        _ ↔ a = 2*b := by ring_nf
    exact equiv.mp ev2_eqs.1

  -- Since $a + b = L$ and $a = 2b$: $b = \frac{L}{3}$.
  have L_from_b : L = 3*b := by
    simp [L]; rw [a_from_b]; ring

  -- At Event 3, they meet at midpoint $\frac{L}{2}$:
  have event3_eq1 : (a - L/2) / E₂_vₜ = (L/2 - ΔDₚ₂ - ΔDₚ₁) / vₚ := by
    obtain ⟨Δt, ⟨f,g⟩⟩ := ev₃
    have pos1 : a - L/2 > 0 := by linarith
    have pos2 : L/2 - ΔDₚ₂ - ΔDₚ₁ > 0 := by simp [ΔDₚ₁]; rw [Dp_at_2]; linarith
    have pos3 : E₂_vₜ > 0 := by exact half_pos vₜ_pos
    rw [← g pos2 vₚ_pos, ← f pos1 pos3]


  have h_b : b = 75 := by
    /- Using the relation from Event 1 ($\frac{b}{v_e} = \frac{45\text{ km}}{v_p}$), we get:
      \begin{align}
        v_p &= \frac{45 \text{ km} \cdot v_e}{b}
      \end{align} -/
    have eq1 : vₚ = (45 * vₑ)/b := by
      have equiv := by
        calc
          b/vₑ = ΔDₚ₁/vₚ
          _ ↔ vₚ*(b/vₑ) = vₚ*(ΔDₚ₁/vₚ) := by exact Iff.symm (mul_left_cancel_iff_of_pos vₚ_pos)
          _ ↔ (vₚ*b)/vₑ = ΔDₚ₁ := by field_simp
          _ ↔ vₑ*((vₚ*b)/vₑ) = vₑ*ΔDₚ₁ := by exact Iff.symm (mul_left_cancel_iff_of_pos vₑ_pos)
          _ ↔ vₚ*b = vₑ*ΔDₚ₁ := by field_simp
          _ ↔ (vₚ*b)/b = (vₑ*ΔDₚ₁)/b := by exact Iff.symm (div_left_inj' (Ne.symm (ne_of_lt b_pos)))
          _ ↔ vₚ = (vₑ*ΔDₚ₁)/b := by field_simp
          _ ↔ vₚ = (45 * vₑ)/b := by simp [ΔDₚ₁]; ring_nf
      apply equiv.mp ev1_eqs.2

    /- From $\frac{b}{v_e} = \frac{a}{v_t} = \frac{2b}{v_t}$, we get:
      \begin{align}
        v_t &= \frac{2b \cdot v_e}{b} = 2v_e
      \end{align}-/
    have eq2 : vₜ = 2*vₑ := by
      calc
        vₜ = (a*vₑ)/b := by rw [vₜ_eq1]
        _  = ((2*b)*vₑ)/b := by rw [a_from_b]
        _  = ((2*vₑ)*b)/b := by ring_nf
        _  = 2*vₑ := by field_simp

    /- Since they meet, these times are equal:
      \begin{align}
        \frac{b}{v_t} &= \frac{\frac{3b}{2} - 90 \text{ km}}{v_p} \\
        b \cdot v_p &= v_t \cdot \left(\frac{3b}{2} - 90\text{ km}\right)
      \end{align} -/
    have eq3 : b/vₜ = ((3*b)/2 - 90)/vₚ := by
        calc
        b/vₜ
        _ = (b/2)/(vₜ/2) := by field_simp
        _ = ((4*b - 3*b)/2)/(vₜ/2) := by ring
        _ = (2*b - (3*b)/2)/(vₜ/2) := by ring
        _ = (a - L/2)/(vₜ/2) := by rw [L_from_b, a_from_b]
        _ = (a - L/2)/E₂_vₜ := by simp [E₂_vₜ]
        _ = (L/2 - ΔDₚ₂ - ΔDₚ₁) / vₚ := by rw [event3_eq1]
        _ = ((3*b)/2 - ΔDₚ₂ - ΔDₚ₁) / vₚ := by rw [L_from_b]
        _ = ((3*b)/2 - (ΔDₚ₂ + ΔDₚ₁)) / vₚ := by ring
        _ = ((3*b)/2 - 90)/vₚ := by simp [ΔDₚ₁]; rw [Dp_at_2]; norm_num
    have eq4 : b * vₚ = ((3*b)/2 - 90)*vₜ := by
      refine mul_eq_mul_of_div_eq_div b _ ?_ ?_ eq3
      . exact Ne.symm (ne_of_lt vₜ_pos)
      . exact Ne.symm (ne_of_lt vₚ_pos)

    /- Substituting these into our meeting time equation:
      \begin{align}
        b \cdot \frac{45\text{ km} \cdot v_e}{b} &= 2v_e \cdot \left(\frac{3b}{2} - 90\text{ km}\right) \\
        ...
        b &= 75\text{ km}
      \end{align}
    -/
    have equiv := by
      calc
        b * vₚ = ((3*b)/2 - 90)*vₜ
        _ ↔ b * vₚ = vₜ*((3*b)/2 - 90) := by ring_nf
        _ ↔ b * ((45 * vₑ)/b) = (2*vₑ)*((3*b)/2 - 90) := by rw [eq1, eq2]
        _ ↔ 45 * vₑ = (2*vₑ)*((3*b)/2 - 90) := by field_simp
        _ ↔ vₑ*45 = vₑ*(2*((3*b)/2 - 90)) := by ring_nf
        _ ↔ 45 = 2*((3*b)/2 - 90) := by exact mul_left_cancel_iff_of_pos vₑ_pos
        _ ↔ 45 = (2*3*b)/2 - 2*90 := by ring_nf
        _ ↔ 45 = 3*b - 2*90 := by ring_nf
        _ ↔ 45 = 3*b - 180 := by ring_nf
        _ ↔ 45 + 180 = 3*b := by exact eq_sub_iff_add_eq
        _ ↔ 3*75 = 3*b := by norm_num
        _ ↔ 75 = b := by field_simp
        _ ↔ b = 75 := by exact eq_comm
    apply equiv.mp eq4

  /- Since $a = 2b$:
    \begin{align}
      a &= 2 \cdot 75 \text{ km} = 150\text{ km}
    \end{align}

    Therefore:
    \begin{align}
      L &= a + b = 150 \text{ km}+ 75 \text{ km}= 225 \text{ km}
    \end{align} -/
  simp [L]
  rw [a_from_b]
  rw [h_b]
  norm_num