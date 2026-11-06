import Mathlib


set_option maxHeartbeats 300000
theorem inequalities_237192 (x y z : ℝ) (h : x * y + y * z + z * x = 1) :
    (x > 0 ∧ y > 0 ∧ z > 0 → (x ^ 2 / (1 + x ^ 2) + y ^ 2 / (1 + y ^ 2) + z ^ 2 / (1 + z ^ 2)) < 1) ∧
    ((x ^ 2 / (1 + x ^ 2) + y ^ 2 / (1 + y ^ 2) + z ^ 2 / (1 + z ^ 2)) < 1 ↔
      (x > 0 ∧ y >  0 ∧ z > 0) ∨
      (x < 0 ∧ y < 0 ∧ z < 0)) := by 

      --We first rewrite S to 1 - (2xyz) / ((x+y)(y+z)(z+x)).
      have eq1 : 1 + x^2 = (x+y)*(x+z) := by 
        rw [← h]
        ring
      have eq2 : 1 + y^2 = (y+x)*(y+z) := by
        rw [← h]
        ring
      have eq3 : 1 + z^2 = (z+x)*(z+y) := by
        rw [← h]
        ring

      have : (x+y) ≠ 0 := by
        by_contra e
        rw [e] at eq1
        field_simp at eq1
        nlinarith
      have : (x+z) ≠ 0 := by
        by_contra e
        rw [e] at eq1
        field_simp at eq1
        nlinarith
      have : (y+z) ≠ 0 := by
        by_contra e
        rw [e] at eq2
        field_simp at eq1
        nlinarith
      have : (z+x) ≠ 0 := by rw [add_comm]; assumption
      have : (y+x) ≠ 0 := by rw [add_comm]; assumption
      have : (z+y) ≠ 0 := by rw [add_comm]; assumption

      rw [eq1,eq2,eq3]
      have eq : x ^ 2 / ((x + y) * (x + z)) + y ^ 2 / ((y + x) * (y + z)) + z ^ 2 / ((z + x) * (z + y)) = 1 - (2*x*y*z / ((x+y)*(y+z)*(z+x))) := by 
        field_simp
        ring
      rw [eq]


      constructor

      --The first claim
      --If all three numbers are positive or negative, then S<1.
      --This simply follows from that (2xyz) / ((x+y)(y+z)(z+x)) > 0.
      intro ⟨hx,hy,hz⟩
      have : 0 < 2 * x * y * z / ((x + y) * (y + z) * (z + x)) := by positivity
      linarith

      --For the second claim
      --We need to show if S<1, then either all three numbers are positive or all three numbers are negative.
      --This follows from that if (2xyz) / ((x+y)(y+z)(z+x)) > 0, then all three numbers must be positive or negative.
      constructor
      --From left to right
      intro h

      have xne0 : x ≠ 0 := by 
        by_contra xe0
        rw [xe0] at h
        norm_num at h
      have yne0 : y ≠ 0 := by
        by_contra ye0
        rw [ye0] at h
        norm_num at h
      have zne0 : z ≠ 0 := by
        by_contra ze0
        rw [ze0] at h
        norm_num at h
      
      have : 0 < 2 * x * y * z / ((x + y) * (y + z) * (z + x)) := by linarith
      have : ((x + y) * (y + z) * (z + x))  ≠ 0 := by positivity
      have cla : (0 < x * y * z ∧ 0 < ((x + y) * (y + z) * (z + x))) ∨ (x * y * z < 0 ∧ ((x + y) * (y + z) * (z + x) <0)) := by 
        by_cases nupos : 0 < x * y * z
        have nu: 0 < 2 * x * y * z := by linarith
        have : 0 < ((x + y) * (y + z) * (z + x)) := by 
          by_contra neg
          push_neg at neg
          have de: ((x + y) * (y + z) * (z + x)) < 0 := by 
            by_contra nneg
            push_neg at nneg
            have : ((x + y) * (y + z) * (z + x)) = 0 := by linarith
            contradiction
          have : 2 * x * y * z / ((x + y) * (y + z) * (z + x)) < 0 := by exact div_neg_of_pos_of_neg nu de
          linarith
        left
        constructor; exact nupos; exact this

        have nuneg : x*y*z < 0 := by 
          push_neg at nupos
          have : x*y*z ≠ 0 := by positivity
          by_contra nneg
          push_neg at nneg
          have : x*y*z = 0 := by linarith
          contradiction
        have nuneg': 2*x*y*z < 0 := by linarith
        have deneg : (x + y) * (y + z) * (z + x) < 0 := by 
          by_contra nneg
          push_neg at nneg
          have : 0 < (x + y) * (y + z) * (z + x) := by positivity
          have : 2 * x * y * z / ((x + y) * (y + z) * (z + x)) < 0 := by exact div_neg_of_neg_of_pos nuneg' this
          linarith
        right;
        constructor; exact nuneg; exact deneg
      
      by_cases xpos : 0 < x
      
      by_cases ypos : 0 < y
      have : 0 < z := by
        by_contra znpos
        push_neg at znpos
        have : z < 0 := by exact lt_of_le_of_ne znpos zne0
        rcases cla with ⟨c1,c2⟩ | ⟨c1,c2⟩ 
        nlinarith
        nlinarith
      tauto

      exfalso
      have yneg: y<0 := by 
        push_neg at ypos
        exact lt_of_le_of_ne ypos yne0
      rcases cla with ⟨c1,c2⟩ | ⟨c1,c2⟩
      have : z < 0 := by nlinarith
      nlinarith
      have : 0 < z := by nlinarith
      nlinarith

      have xneg : x < 0 := by push_neg at xpos; exact lt_of_le_of_ne xpos xne0
      by_cases ypos : 0 < y
      exfalso
      rcases cla with ⟨c1,c2⟩ | ⟨c1,c2⟩
      have : z < 0 := by nlinarith
      nlinarith [c2]
      have : 0 < z := by nlinarith
      nlinarith [c2]

      have yneg : y < 0 := by push_neg at ypos; exact lt_of_le_of_ne ypos yne0
      have zneg : z < 0 := by  
        rcases cla with ⟨c1,c2⟩ | ⟨c1,c2⟩
        nlinarith
        nlinarith
      tauto


      --From right to left
      --A simple verification that if x y z are of the same sign, then (2xyz) / ((x+y)(y+z)(z+x)) > 0.
      intro h
      rcases h with ⟨hx,hy,hz⟩ | ⟨hx,hy,hz⟩
      have : 0 < 2 * x * y * z / ((x + y) * (y + z) * (z + x)) := by 
        have t1: 0 < 2 * x * y * z := by positivity
        have t2: 0< ((x + y) * (y + z) * (z + x)) := by nlinarith
        exact div_pos t1 t2
      linarith

      have : 0 < 2 * x * y * z / ((x + y) * (y + z) * (z + x)) := by 
        have nu: 2 * x * y * z < 0 := by 
          have : 0< x*y := by nlinarith
          nlinarith
        have de: (x + y) * (y + z) * (z + x) <0 := by nlinarith
        exact div_pos_of_neg_of_neg nu de
      linarith
