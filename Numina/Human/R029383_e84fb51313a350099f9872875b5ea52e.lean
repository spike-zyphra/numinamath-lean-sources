import Mathlib
/-Given that $a$, $b$, and $c$ are nonzero real numbers, find all possible values of the expression
\[\frac{a}{|a|} + \frac{b}{|b|} + \frac{c}{|c|} + \frac{abc}{|abc|}.\]Enter all possible values, separated by commas.-/
theorem algebra_3844 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c) = 4 ∨
    a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c) = 0 ∨
    a / abs a + b / abs b + c / abs c + a * b * c / abs (a * b * c) = -4 := by 
    -- simp the multiple of abc
    rw [abs_mul,abs_mul]
    -- consider 8 cases
    by_cases haa: 0 < a<;>
    by_cases hbb: 0 < b<;>
    by_cases hcc: 0 < c
    -- use haa hbb hbc to simp
    simp [abs_of_pos haa,abs_of_pos hbb,abs_of_pos hcc]
    field_simp
    norm_num
    -- use hcc to simp
    push_neg at hcc
    simp [abs_of_pos haa,abs_of_pos hbb,abs_of_nonpos hcc]
    field_simp
    -- use hbb to simp
    push_neg at hbb
    simp [abs_of_pos haa,abs_of_nonpos hbb,abs_of_pos hcc]
    field_simp
    -- b<0 c<0
    push_neg at hbb hcc
    simp [abs_of_pos haa,abs_of_nonpos hbb,abs_of_nonpos hcc]
    field_simp
    -- a<0
    push_neg at haa
    simp [abs_of_nonpos haa,abs_of_pos hbb,abs_of_pos hcc]
    field_simp
    -- use hcc to simp
    push_neg at hcc haa
    simp [abs_of_nonpos haa,abs_of_pos hbb,abs_of_nonpos hcc]
    field_simp
    -- use hbb to simp
    push_neg at hbb haa
    simp [abs_of_nonpos haa,abs_of_nonpos hbb,abs_of_pos hcc]
    field_simp
    -- b<0 c<0
    push_neg at hbb hcc haa
    simp [abs_of_nonpos haa,abs_of_nonpos hbb,abs_of_nonpos hcc]
    field_simp
    norm_num

    

    
    