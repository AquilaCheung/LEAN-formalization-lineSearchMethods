import MIL.C10_Linear_Algebra.S01_Vector_Spaces
import MIL.C10_Linear_Algebra.S02_Subspaces

open Classical
open BigOperators

-- part 2 : mathematical foundations

abbrev Vec (n : ℕ) := Fin n → ℝ

variable {n : ℕ}
variable (f : Vec n → ℝ)

def innerpro (x y : Vec n) : ℝ :=
  ∑ i : Fin n, x i * y i

axiom innerproSelfPos (x : Vec n) :
  innerpro x x > 0

axiom normSqEqInner (x : Vec n) :
  (norm x)^2 = innerpro x x

axiom cauchySchwarz (x y : Vec n) :
  innerpro x y ≤ norm x * norm y

variable (grad : Vec n → Vec n)

axiom grad_lipschitz
  (L : ℝ) (hL : L > 0) (x y : Vec n) :
  norm (grad x - grad y) ≤ L * norm (fun i => x i - y i)

axiom first_order_approx (x d : Vec n) :
  ∃ ε > 0,
    ∀ α ∈ Set.Ioo (0 : ℝ) ε,
      f (fun i => x i + α * d i)
        < f x + α * innerpro (grad x) d

-- part 3 : descent and line search conditions

def isDescentDirection (x d : Vec n) : Prop :=
  innerpro (grad x) d < 0

lemma negGradIsDescent (x : Vec n) :
  isDescentDirection grad x (- grad x) := by
  unfold isDescentDirection
  have hpos :
      innerpro (grad x) (grad x) > 0 :=
    innerproSelfPos (grad x)
  have hneg :
      innerpro (grad x) (-grad x)
        = - innerpro (grad x) (grad x) := by
    simp [innerpro]
  have :
      - innerpro (grad x) (grad x) < 0 := by
    simpa using hpos
  simpa [hneg] using this

lemma descentImpliesDecrease
  (x d : Vec n)
  (hdesc : isDescentDirection grad x d) :
  ∃ α > 0, f (fun i => x i + α * d i) < f x := by
  unfold isDescentDirection at hdesc
  obtain ⟨ε, hεpos, hε⟩ :=
    first_order_approx f grad x d
  have hαpos : ε / 2 > 0 :=
    half_pos hεpos
  have hαrange :
      ε / 2 ∈ Set.Ioo (0 : ℝ) ε := by
    constructor
    · exact hαpos
    · have : ε / 2 < ε := by linarith
      exact this
  have hmain := hε (ε / 2) hαrange
  have hneg :
      (ε / 2) * innerpro (grad x) d < 0 :=
    mul_neg_of_pos_of_neg hαpos hdesc
  have :
      f (fun i => x i + (ε / 2) * d i) < f x := by
    linarith
  refine ⟨ε / 2, hαpos, ?_⟩
  exact this

-- armijo

def armijo (x d : Vec n) (α c1 : ℝ) : Prop :=
  f (fun i => x i + α * d i)
    ≤ f x + c1 * α * innerpro (grad x) d

lemma existsArmijoStep
  (x d : Vec n) (c1 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1) :
  ∃ α > 0, armijo f grad x d α c1 := by
  unfold isDescentDirection at hdesc
  obtain ⟨ε, hεpos, hε⟩ :=
    first_order_approx f grad x d
  let α := ε / 2
  have hαpos : α > 0 := by
    exact half_pos hεpos
  have hαrange :
      α ∈ Set.Ioo (0 : ℝ) ε := by
    constructor
    · exact hαpos
    · dsimp [α]; linarith
  have hmain := hε α hαrange
  have hscale :
      α * innerpro (grad x) d
        ≤ c1 * α * innerpro (grad x) d := by
    have hc1lt : c1 < 1 := hc1.2
    have hneg : innerpro (grad x) d < 0 := hdesc
    have hneg2 :
        α * innerpro (grad x) d < 0 :=
      mul_neg_of_pos_of_neg hαpos hneg
    have : (1 : ℝ) ≥ c1 := by linarith
    have :=
      mul_le_mul_of_nonpos_right this (le_of_lt hneg2)
    simpa [mul_assoc] using this
  have :
      f (fun i => x i + α * d i)
        ≤ f x + c1 * α * innerpro (grad x) d := by
    linarith
  refine ⟨α, hαpos, ?_⟩
  exact this

-- backtracking

def backtrackStep (γ : ℝ) (α : ℝ) : ℝ :=
  γ * α

def backtrackPow (γ α0 : ℝ) (k : ℕ) : ℝ :=
  (γ ^ k) * α0

def existsBacktrackingStep
  (x d : Vec n) (c1 γ α0 : ℝ) : Prop :=
  ∃ k : ℕ,
    armijo f grad x d (backtrackPow γ α0 k) c1

axiom backtrackingFindsStep
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0) :
  ∃ k : ℕ,
    armijo f grad x d (backtrackPow γ α0 k) c1

noncomputable def btIndex
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0) : ℕ :=
  Classical.choose
    (backtrackingFindsStep
      f grad x d c1 γ α0 hdesc hc1 hγ hα0)

noncomputable def btAlpha
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0) : ℝ :=
  backtrackPow γ α0
    (btIndex f grad x d c1 γ α0 hdesc hc1 hγ hα0)

lemma btAlphaPos
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0) :
  btAlpha f grad x d c1 γ α0 hdesc hc1 hγ hα0 > 0 := by
  unfold btAlpha
  have hγpos : 0 < γ := hγ.1
  have hpow :
      0 < γ ^ (btIndex f grad x d c1 γ α0 hdesc hc1 hγ hα0) :=
    pow_pos hγpos _
  exact mul_pos hpow hα0


variable (x0 : Vec n)

def descent_dir (x : Vec n) : Vec n :=
  - grad x

def update (x d : Vec n) (α : ℝ) : Vec n :=
  fun i => x i + α * d i

noncomputable def next_x
  (x : Vec n) (c1 γ α0 : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hdesc : isDescentDirection grad x (-grad x)) :
  Vec n :=
  update x (-grad x)
    (btAlpha f grad x (-grad x) c1 γ α0 hdesc hc1 hγ hα0)

noncomputable def x_seq
  (c1 γ α0 : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hdesc_all : ∀ x, isDescentDirection grad x (-grad x)) :
  ℕ → Vec n
| 0 => x0
| (k+1) =>
  let xk := x_seq c1 γ α0 hc1 hγ hα0 hdesc_all k
  next_x f grad xk c1 γ α0 hc1 hγ hα0 (hdesc_all xk)
termination_by k => k

lemma update_eq_fun (x d : Vec n) (α : ℝ) :
  update x d α = (fun i => x i + α * d i) :=
  rfl

lemma oneStepDescent
  (x : Vec n)
  (c1 γ α0 : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hdesc : isDescentDirection grad x (-grad x)) :
  f (next_x f grad x c1 γ α0 hc1 hγ hα0 hdesc)
  ≤ f x := by
  unfold next_x

  let α :=
    btAlpha f grad x (-grad x) c1 γ α0 hdesc hc1 hγ hα0


  have hαdef :
    α =
      backtrackPow γ α0
        (Classical.choose
          (backtrackingFindsStep
            f grad x (-grad x) c1 γ α0 hdesc hc1 hγ hα0)) := rfl

  have hA :=
    Classical.choose_spec
      (backtrackingFindsStep
        f grad x (-grad x) c1 γ α0 hdesc hc1 hγ hα0)

  unfold armijo at hA

  have hA' :
    f (fun i => x i + -(α * grad x i))
      ≤ f x + c1 * α * innerpro (grad x) (-grad x) := by
    rw [← hαdef] at hA
    simpa [neg_mul] using hA

  have hinner : innerpro (grad x) (-grad x) < 0 :=
    hdesc

  have hαpos :
    α > 0 :=
    btAlphaPos f grad x (-grad x) c1 γ α0 hdesc hc1 hγ hα0

  have hprod :
    c1 * α * innerpro (grad x) (-grad x) < 0 := by
    have h1 : 0 < c1 := hc1.1
    have h12 : 0 < c1 * α := mul_pos h1 hαpos
    exact mul_neg_of_pos_of_neg h12 hinner

  have hprod_le :
    c1 * α * innerpro (grad x) (-grad x) ≤ 0 :=
    le_of_lt hprod

  have hfinal :
    f (fun i => x i + -(α * grad x i)) ≤ f x := by
    have := hA'
    linarith

  rw [update_eq_fun]

  have hfinal' :
    f (fun i => x i + α * (-grad x i)) ≤ f x := by
    simpa [neg_mul] using hfinal

  exact hfinal'

def goldstein (x d : Vec n) (α c : ℝ) : Prop :=
  f (fun i => x i + α * d i)
    ≤ f x + c * α * innerpro (grad x) d
  ∧
  f (fun i => x i + α * d i)
    ≥ f x + (1 - c) * α * innerpro (grad x) d

lemma goldsteinImpliesArmijo
  (x d : Vec n) (α c : ℝ)
  (h : goldstein f grad x d α c) :
  armijo f grad x d α c := by
  unfold goldstein at h
  unfold armijo
  exact h.1

lemma armijoImpliesStrictDecrease
  (x d : Vec n)
  (α c1 : ℝ)
  (hA : armijo f grad x d α c1)
  (hdesc : isDescentDirection grad x d)
  (hα : α > 0)
  (hc1 : c1 > 0) :
  f (fun i => x i + α * d i) < f x := by
  unfold armijo at hA
  unfold isDescentDirection at hdesc

  -- hA : f(x+αd) ≤ f x + c1 * α * ⟨∇f, d⟩
  -- hdesc : ⟨∇f, d⟩ < 0

  have hneg :
    c1 * α * innerpro (grad x) d < 0 := by
    have hpos : c1 * α > 0 := mul_pos hc1 hα
    exact mul_neg_of_pos_of_neg hpos hdesc

  have :
    f (fun i => x i + α * d i) < f x := by
    have := hA
    linarith

  exact this

def wolfe (x d : Vec n) (α c1 c2 : ℝ) : Prop :=
  f (fun i => x i + α * d i)
    ≤ f x + c1 * α * innerpro (grad x) d
  ∧
  innerpro (grad (fun i => x i + α * d i)) d
    ≥ c2 * innerpro (grad x) d

lemma innerpro_sub_left (x y d : Vec n) :
  innerpro (fun i => x i - y i) d
    = innerpro x d - innerpro y d := by
  unfold innerpro
  simp [sub_mul, Finset.sum_sub_distrib]

lemma wolfeImpliesArmijo
  (x d : Vec n) (α c1 c2 : ℝ)
  (h : wolfe f grad x d α c1 c2) :
  armijo f grad x d α c1 := by
  unfold wolfe at h
  unfold armijo
  exact h.1

lemma wolfeCurvatureIneqMain
  (f : Vec n → ℝ)
  (grad : Vec n → Vec n)
  (x d : Vec n) (α c1 c2 : ℝ)
  (h : wolfe f grad x d α c1 c2) :
  innerpro (grad (fun i => x i + α * d i) - grad x) d
    ≥ (c2 - 1) * innerpro (grad x) d := by
  unfold wolfe at h

  have hcurv :
    innerpro (grad (fun i => x i + α * d i)) d
      ≥ c2 * innerpro (grad x) d :=
    h.2

  have h1 :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      =
    innerpro (grad (fun i => x i + α * d i)) d
      - innerpro (grad x) d :=
    innerpro_sub_left _ _ _

  have h2 :
    innerpro (grad (fun i => x i + α * d i)) d
      - innerpro (grad x) d
    ≥
    c2 * innerpro (grad x) d
      - innerpro (grad x) d :=
    sub_le_sub_right hcurv _

  have h3 :
    c2 * innerpro (grad x) d
      - innerpro (grad x) d
    =
    (c2 - 1) * innerpro (grad x) d := by
    ring

  simpa [h1, h3] using h2


lemma lipschitzUpperBound
  (x d : Vec n)
  (α L : ℝ)
  (hL : L > 0)
  (hα : α ≥ 0) :
  innerpro (grad (fun i => x i + α * d i) - grad x) d
    ≤ L * α * (norm d)^2 := by

  have hlip :=
    grad_lipschitz grad L hL
      (fun i => x i + α * d i) x

  have hdiff :
    (fun i => (fun i => x i + α * d i) i - x i)
      =
    (fun i => α * d i) := by
    funext i
    simp

  have hlip' :
    norm (grad (fun i => x i + α * d i) - grad x)
      ≤ L * norm (fun i => α * d i) := by
    simpa [hdiff] using hlip

  have hnorm :
    norm (fun i => α * d i) = |α| * norm d :=
    norm_smul α d

  have hcs :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      ≤
    norm (grad (fun i => x i + α * d i) - grad x)
      * norm d :=
    cauchySchwarz _ _

  have hcombine :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      ≤
    (L * norm (fun i => α * d i)) * norm d := by

    have hnonneg : 0 ≤ norm d :=
      norm_nonneg d

    have hmul :
      norm (grad (fun i => x i + α * d i) - grad x) * norm d
        ≤
      (L * norm (fun i => α * d i)) * norm d :=
      mul_le_mul_of_nonneg_right hlip' hnonneg

    exact le_trans hcs hmul

  have hcombine' :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      ≤
    (L * (|α| * norm d)) * norm d := by
    simpa [hnorm] using hcombine

  have hfinal :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      ≤
    L * |α| * (norm d)^2 := by
    ring_nf at hcombine'
    simpa [pow_two] using hcombine'

  have habs : |α| = α :=
    abs_of_nonneg hα

  simpa [habs] using hfinal


lemma alpha_lower_bound_mul
  (x d : Vec n)
  (α c1 c2 L : ℝ)
  (hL : L > 0)
  (hα : α ≥ 0)
  (hw : wolfe f grad x d α c1 c2) :
  (c2 - 1) * innerpro (grad x) d
    ≤ L * α * (norm d)^2 := by

  have h1 :
    (c2 - 1) * innerpro (grad x) d
      ≤ innerpro (grad (fun i => x i + α * d i) - grad x) d := by
    exact
      wolfeCurvatureIneqMain f grad x d α c1 c2 hw

  have h2 :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      ≤ L * α * (norm d)^2 := by
    exact
      (lipschitzUpperBound
        (grad := grad)
        (x := x) (d := d)
        (α := α) (L := L)
        (hL := hL) (hα := hα))

  exact le_trans h1 h2


lemma div_le_of_le_mul
  {a b c : ℝ}
  (hc : 0 < c)
  (h : a ≤ b * c) :
  a / c ≤ b := by

  have :=
    mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hc))


  have hcne : c ≠ 0 :=
    ne_of_gt hc

  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hcne]
    using this


lemma alpha_lower_bound
  (x d : Vec n)
  (α c1 c2 L : ℝ)
  (hL : L > 0)
  (hα : α ≥ 0)
  (hposd : norm d ≠ 0)
  (hw : wolfe f grad x d α c1 c2) :
  α ≥
    ((1 - c2) * (- innerpro (grad x) d))
      / (L * (norm d)^2) := by


  have hmain :=
    alpha_lower_bound_mul f grad x d α c1 c2 L hL hα hw


  have hineq :
    (1 - c2) * (- innerpro (grad x) d)
      ≤ (L * (norm d)^2) * α := by
    linarith

  have hden_pos : 0 < L * (norm d)^2 := by
    have hpos : norm d > 0 :=
      lt_of_le_of_ne (norm_nonneg d) (by
        intro h
        apply hposd
        exact h.symm)
    have : 0 < (norm d)^2 :=
      pow_pos hpos 2
    exact mul_pos hL this

  have hineq' :
    (1 - c2) * (- innerpro (grad x) d)
      ≤ α * (L * (norm d)^2) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hineq

  have :=
    div_le_of_le_mul hden_pos hineq'

  exact this


lemma innerpro_neg_grad
  (grad : Vec n → Vec n)
  (x : Vec n) :
  innerpro (grad x) (-grad x)
    = - innerpro (grad x) (grad x) := by

  unfold innerpro

  have h1 :
    (∑ i, grad x i * (- grad x i))
      = ∑ i, - (grad x i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring

  have h2 :
    ∑ i, - (grad x i)^2
      = - ∑ i, (grad x i)^2 := by
    simp

  have hsq :
    innerpro (grad x) (grad x)
      = ∑ i, (grad x i)^2 := by
    unfold innerpro
    apply Finset.sum_congr rfl
    intro i hi
    ring

  calc
    ∑ i, grad x i * (- grad x i)
        = ∑ i, - (grad x i)^2 := h1
    _   = - ∑ i, (grad x i)^2 := h2
    _   = - innerpro (grad x) (grad x) := by
      simp [hsq]



lemma alpha_lower_bound_neg_grad
  (x : Vec n)
  (α c1 c2 L : ℝ)
  (hL : L > 0)
  (hα : α ≥ 0)
  (hpos : norm (grad x) ≠ 0)
  (hw : wolfe f grad x (-grad x) α c1 c2) :
  α ≥ (1 - c2) / L :=
by
  have hmain :=
    alpha_lower_bound f grad x (-grad x) α c1 c2 L
      hL hα
      (by
        simpa [norm_neg] using hpos)
      hw

  have hinner :
    innerpro (grad x) (-grad x)
      = - innerpro (grad x) (grad x) :=
    innerpro_neg_grad grad x

  have hmain' :
    α ≥ (1 - c2) * innerpro (grad x) (grad x) /
          (L * innerpro (grad x) (grad x)) :=
  by
    simpa
      [hinner, norm_neg, normSqEqInner,
       mul_comm, mul_left_comm, mul_assoc]
      using hmain

  let A := innerpro (grad x) (grad x)

  have hApos : A ≠ 0 :=
  by
    intro h
    apply hpos
    have : (norm (grad x))^2 = 0 :=
    by
      simpa [normSqEqInner] using h
    have : norm (grad x) = 0 :=
      pow_eq_zero this
    exact this

  have :
    α ≥ (1 - c2) * A / (L * A) :=
    hmain'

  have hL_ne : L ≠ 0 :=
    ne_of_gt hL

  have hfinal :
    (1 - c2) * A / (L * A)
      = (1 - c2) / L :=
  by
    field_simp [hApos, hL_ne]
    ring

  simpa [hfinal] using this


noncomputable def cos_theta
  (grad : Vec n → Vec n)
  (x d : Vec n) : ℝ :=
  - innerpro (grad x) d /
    (norm (grad x) * norm d)

lemma cos_theta_nonneg
  (x d : Vec n)
  (hdesc : innerpro (grad x) d < 0)
  (hgrad_pos : 0 < norm (grad x))
  (hd_pos : 0 < norm d) :
  0 ≤ cos_theta grad x d :=
by
  unfold cos_theta

  have hnum : 0 < - innerpro (grad x) d :=
  by
    linarith

  have hden : 0 < norm (grad x) * norm d :=
    mul_pos hgrad_pos hd_pos

  exact div_nonneg hnum.le hden.le

lemma innerproCosThetaIdentity
  (x d : Vec n)
  (hgrad : norm (grad x) ≠ 0)
  (hd : norm d ≠ 0) :
  (innerpro (grad x) d)^2
    =
    (cos_theta grad x d)^2
      * (norm (grad x))^2
      * (norm d)^2 :=
by
  unfold cos_theta
  field_simp [hgrad, hd]
  ring


lemma one_step_decrease_armijo
  (x d : Vec n)
  (α c1 : ℝ)
  (hA : armijo f grad x d α c1)
  (hdesc : innerpro (grad x) d < 0)
  (hα : α > 0)
  (hc1 : 0 < c1) :
  f (fun i => x i + α * d i) ≤ f x :=
by
  unfold armijo at hA

  have hneg :
      c1 * α * innerpro (grad x) d ≤ 0 :=
  by
    have hpos : 0 < c1 * α :=
      mul_pos hc1 hα
    exact le_of_lt (mul_neg_of_pos_of_neg hpos hdesc)

  have hrhs :
      f x + c1 * α * innerpro (grad x) d ≤ f x :=
  by
    linarith

  exact le_trans hA hrhs


lemma zoutendijkStepCore
  (x d : Vec n)
  (α c1 c2 L : ℝ)
  (hL : L > 0)
  (hwolfe : wolfe f grad x d α c1 c2)
  (hdesc : innerpro (grad x) d < 0)
  (hd : norm d ≠ 0)
  (hgrad : norm (grad x) ≠ 0)
  (hc1 : 0 < c1)
  (hα_pos : α > 0) :
  f x - f (fun i => x i + α * d i)
    ≥ c1 * (1 - c2) / L
        * (cos_theta grad x d)^2
        * (norm (grad x))^2 :=
by
  have h_armijo : armijo f grad x d α c1 :=
    wolfeImpliesArmijo f grad x d α c1 c2 hwolfe

  unfold armijo at h_armijo

  have h_decrease :
    f x - f (fun i => x i + α * d i)
      ≥ -c1 * α * innerpro (grad x) d :=
  by
    linarith

  have h_alpha_lower :
    α ≥
      (1 - c2) * (-innerpro (grad x) d)
        / (L * (norm d)^2) :=
  by
    apply alpha_lower_bound f grad x d α c1 c2 L hL
    · exact le_of_lt hα_pos
    · exact hd
    · exact hwolfe

  have h_subst :
    -c1 * α * innerpro (grad x) d
      ≥ c1 * (1 - c2) / L
          * (innerpro (grad x) d)^2
          / (norm d)^2 :=
  by
    have h_neg :
      -innerpro (grad x) d > 0 :=
    by
      linarith

    have hnorm_pos :
      norm d > 0 :=
      lt_of_le_of_ne (norm_nonneg d) (Ne.symm hd)

    have h_denom_pos :
      L * (norm d)^2 > 0 :=
      mul_pos hL (pow_pos hnorm_pos 2)

    have h_denom_ne :
      L * (norm d)^2 ≠ 0 :=
      ne_of_gt h_denom_pos

    have h5 :
      c1 * α * (-innerpro (grad x) d)
        ≥ c1 *
            ((1 - c2) * (-innerpro (grad x) d)
              / (L * (norm d)^2))
            * (-innerpro (grad x) d) :=
    by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · exact h_alpha_lower
        · linarith
      · linarith

    have h6 :
      c1 *
          ((1 - c2) * (-innerpro (grad x) d)
            / (L * (norm d)^2))
          * (-innerpro (grad x) d)
        =
        c1 * (1 - c2) / L
          * (innerpro (grad x) d)^2
          / (norm d)^2 :=
    by
      field_simp [h_denom_ne]
      ring

    have h_left :
      -c1 * α * innerpro (grad x) d
        = c1 * α * (-innerpro (grad x) d) :=
    by
      ring

    linarith [h_left, h5, h6]

  have h_cos :
    (innerpro (grad x) d)^2 / (norm d)^2
      =
    (cos_theta grad x d)^2
      * (norm (grad x))^2 :=
  by
    unfold cos_theta

    have h_grad_ne :
      norm (grad x) ≠ 0 :=
      hgrad

    have h_d_ne :
      norm d ≠ 0 :=
      hd

    field_simp [h_grad_ne, h_d_ne]
    ring

  calc
    f x - f (fun i => x i + α * d i)
        ≥ -c1 * α * innerpro (grad x) d :=
      h_decrease
    _   ≥ c1 * (1 - c2) / L
            * (innerpro (grad x) d)^2
            / (norm d)^2 :=
      h_subst
    _   = c1 * (1 - c2) / L
            * ((innerpro (grad x) d)^2 / (norm d)^2) :=
      by ring
    _   = c1 * (1 - c2) / L
            * (cos_theta grad x d)^2
            * (norm (grad x))^2 :=
      by
        rw [h_cos]
        ring


axiom f_bounded_below
  (f : Vec n → ℝ) :
  ∃ m : ℝ, ∀ x : Vec n, f x ≥ m


lemma telescope_sum
  (x_seq : ℕ → Vec n) (k : ℕ) :
  ∑ i ∈ Finset.range k,
      (f (x_seq i) - f (x_seq (i + 1)))
    =
  f (x_seq 0) - f (x_seq k) :=
by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring


theorem zoutendijk_theorem
  (c1 γ α0 L c2 : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hL : L > 0)
  (hc2 : 0 < c2 ∧ c2 < 1)
  (hdesc_all : ∀ x, isDescentDirection grad x (-grad x))
  (hwolfe_all :
    ∀ k,
      wolfe f grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all k)
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all k))
        (btAlpha f grad
          (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all k)
          (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all k))
          c1 γ α0
          (hdesc_all _)
          hc1 hγ hα0)
        c1 c2)
  (hα_pos_all :
    ∀ k,
      btAlpha f grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all k)
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all k))
        c1 γ α0
        (hdesc_all _)
        hc1 hγ hα0 > 0)
  (hgrad_ne_zero :
    ∀ k,
      norm (grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all k)) ≠ 0)
  (k : ℕ) :
  ∑ i ∈ Finset.range k,
      (cos_theta grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)))^2
      *
      (norm (grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)))^2
    ≤
      L / (c1 * (1 - c2)) *
        (f x0 - Classical.choose (f_bounded_below f)) :=
by
  classical

  set m := Classical.choose (f_bounded_below f)
  have hm := Classical.choose_spec (f_bounded_below f)

  let x_seq_vec : ℕ → Vec n :=
    fun i =>
      x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i

  have hx0 : x_seq_vec 0 = x0 :=
  by
    simp [x_seq_vec, x_seq]

  have h_step :
    ∀ i,
      f (x_seq_vec i) - f (x_seq_vec (i + 1))
      ≥
        c1 * (1 - c2) / L *
          (cos_theta grad (x_seq_vec i) (-grad (x_seq_vec i)))^2 *
          (norm (grad (x_seq_vec i)))^2 :=
  by
    intro i

    let x_i := x_seq_vec i
    let d_i := -grad x_i
    let α_i :=
      btAlpha f grad x_i d_i c1 γ α0
        (hdesc_all x_i) hc1 hγ hα0

    have h_core :=
      zoutendijkStepCore
        (f := f) (grad := grad)
        (x := x_i) (d := d_i) (α := α_i)
        (c1 := c1) (c2 := c2) (L := L)
        (hL := hL)
        (hwolfe := hwolfe_all i)
        (hdesc := by simpa [d_i] using (hdesc_all x_i))
        (hd := by simpa [d_i] using (hgrad_ne_zero i))
        (hgrad := hgrad_ne_zero i)
        (hc1 := hc1.1)
        (hα_pos := hα_pos_all i)

    have h_update :
      x_seq_vec (i + 1) = update x_i d_i α_i :=
    by
      simp [x_seq_vec, x_seq, next_x, x_i, d_i, α_i]

    have h_core' :
      f x_i - f (update x_i d_i α_i)
        ≥
          c1 * (1 - c2) / L *
            (cos_theta grad x_i d_i)^2 *
            (norm (grad x_i))^2 :=
    by
      simpa using h_core

    have h_step_i :
      f x_i - f (x_seq_vec (i + 1))
        ≥
          c1 * (1 - c2) / L *
            (cos_theta grad x_i d_i)^2 *
            (norm (grad x_i))^2 :=
    by
      simpa [h_update] using h_core'

    simpa [x_i, d_i] using h_step_i

  -- telescope
  have h_tel :=
    telescope_sum (f := f) (x_seq := x_seq_vec) (k := k)

  have h_sum :
    ∑ i ∈ Finset.range k,
        c1 * (1 - c2) / L *
          (cos_theta grad (x_seq_vec i) (-grad (x_seq_vec i)))^2 *
          (norm (grad (x_seq_vec i)))^2
      ≤
    ∑ i ∈ Finset.range k,
        (f (x_seq_vec i) - f (x_seq_vec (i + 1))) :=
  by
    refine Finset.sum_le_sum ?_
    intro i hi
    simpa using (h_step i)

  have h_mid :
    ∑ i ∈ Finset.range k,
        c1 * (1 - c2) / L *
          (cos_theta grad (x_seq_vec i) (-grad (x_seq_vec i)))^2 *
          (norm (grad (x_seq_vec i)))^2
      ≤
    f x0 - f (x_seq_vec k) :=
  by
    simpa [h_tel, hx0] using h_sum

  have h_bound :
    f x0 - f (x_seq_vec k) ≤ f x0 - m :=
  by
    have := hm (x_seq_vec k)
    linarith

  have h_total :=
    le_trans h_mid h_bound

  set S :=
    ∑ i ∈ Finset.range k,
      (cos_theta grad (x_seq_vec i) (-grad (x_seq_vec i)))^2 *
      (norm (grad (x_seq_vec i)))^2

  have h_scaled :
    (c1 * (1 - c2) / L) * S ≤ f x0 - m :=
  by
    simpa
      [S, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      using h_total

  have h_pos_mul :
    0 < c1 * (1 - c2) :=
    mul_pos hc1.1 (sub_pos.mpr hc2.2)

  have h_pos :
    0 < c1 * (1 - c2) / L :=
    div_pos h_pos_mul hL

  have h_inv_pos :
    0 < L / (c1 * (1 - c2)) :=
    div_pos hL h_pos_mul

  have h_mul :=
    mul_le_mul_of_nonneg_left
      h_scaled
      (le_of_lt h_inv_pos)

  have h_cancel :
    (L / (c1 * (1 - c2))) *
      (c1 * (1 - c2) / L) = 1 :=
  by
    have hne : c1 * (1 - c2) ≠ 0 :=
      ne_of_gt h_pos_mul
    field_simp [hne]

  have h_final :
    S ≤ (f x0 - m) * (L / (c1 * (1 - c2))) :=
  by
    have h₁ :
      (L / (c1 * (1 - c2))) *
          (c1 * (1 - c2) / L * S)
        =
      ((L / (c1 * (1 - c2))) *
          (c1 * (1 - c2) / L)) * S :=
    by
      ring

    have h₂ :
      ((L / (c1 * (1 - c2))) *
        (c1 * (1 - c2) / L)) = 1 :=
      h_cancel

    have h₃ :
      S ≤ (L / (c1 * (1 - c2))) *
            (f x0 - m) :=
    by
      simpa [h₁, h₂] using h_mul

    simpa [mul_comm] using h₃

  simpa [S, m, mul_comm] using h_final






axiom subseq_sum_le_full_sum
  {n : ℕ}
  (f : Vec n → ℝ)
  (grad : Vec n → Vec n)
  (x0 : Vec n)
  (c1 γ α0 : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hdesc_all : ∀ x, isDescentDirection grad x (-grad x))
  (φ : ℕ → ℕ)
  (hmono : StrictMono φ)
  (K : ℕ) :
  ∑ i ∈ Finset.range K,
      cos_theta grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all (φ i))
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all (φ i))) ^ 2 *
      ‖grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all (φ i))‖ ^ 2
  ≤
  ∑ i ∈ Finset.range (φ K),
      cos_theta grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)) ^ 2 *
      ‖grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)‖ ^ 2



theorem globalConvergenceCore
  (n : ℕ)
  (f : Vec n → ℝ)
  (grad : Vec n → Vec n)
  (x0 : Vec n)
  (c1 γ α0 L : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hdesc_all : ∀ x, isDescentDirection grad x (-grad x))

  -- Zoutendijk bound
  (hZ :
    ∀ k,
      ∑ i ∈ Finset.range k,
        cos_theta grad
          (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)
          (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)) ^ 2 *
        ‖grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)‖ ^ 2
      ≤ L)
  (ε : ℝ)
  (hε : ε > 0)
  (φ : ℕ → ℕ)
  (hmono : StrictMono φ)
  (hlower :
    ∀ k,
      ‖grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all (φ k))‖ ^ 2 ≥ ε ^ 2)
  (hcos :
    ∀ k,
      cos_theta grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all (φ k))
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all (φ k))) ^ 2 = 1)

  :

  False := by

  let a : ℕ → ℝ :=
    fun k =>
      cos_theta grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all (φ k))
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all (φ k))) ^ 2 *
      ‖grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all (φ k))‖ ^ 2

  -- 每项 ≥ ε²
  have hterm : ∀ k, a k ≥ ε ^ 2 := by
    intro k
    have h1 := hcos k
    have h2 := hlower k
    simp [a, h1]
    exact h2

  -- 前缀和 ≥ K * ε²
  have hsum_lower :
    ∀ K,
      ∑ i ∈ Finset.range K, a i ≥ (K : ℝ) * ε ^ 2 := by
    intro K
    induction K with
    | zero =>
        simp
    | succ K ih =>
        have hK := hterm K
        have hsum :=
          Finset.sum_range_succ (fun i => a i) K

        simp [hsum]

        have : (∑ i ∈ Finset.range K, a i) + a K
              ≥ (K : ℝ) * ε ^ 2 + ε ^ 2 := by
          exact add_le_add ih hK

        have hrewrite :
          (K : ℝ) * ε ^ 2 + ε ^ 2 = (K + 1 : ℝ) * ε ^ 2 := by
          ring

        simpa [hrewrite]

  have hbounded :
    ∀ K,
      ∑ i ∈ Finset.range K, a i ≤ L := by
    intro K

    have := hZ (φ K)

    have hsubset :
      ∑ i ∈ Finset.range K, a i
      ≤ ∑ i ∈ Finset.range (φ K),
          cos_theta grad
            (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)
            (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)) ^ 2 *
          ‖grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all i)‖ ^ 2 := by
      simpa [a] using
        subseq_sum_le_full_sum
          f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all φ hmono K

    exact le_trans hsubset this

  have hpos : ε ^ 2 > 0 := by
    have := hε
    nlinarith

  let K : ℕ := Nat.succ (Nat.ceil (L / (ε ^ 2)))

  have hK_ge :
    (K : ℝ) ≥ L / (ε ^ 2) + 1 := by
    have hceil : (Nat.ceil (L / (ε ^ 2)) : ℝ) ≥ L / (ε ^ 2) :=
      Nat.le_ceil _
    have : (K : ℝ) = (Nat.ceil (L / (ε ^ 2)) : ℝ) + 1 := by
      simp [K]
    linarith

  have hmul :
    (K : ℝ) * ε ^ 2 ≥ (L / (ε ^ 2) + 1) * ε ^ 2 :=
    mul_le_mul_of_nonneg_right hK_ge (by positivity)

  have hrewrite :
    (L / (ε ^ 2) + 1) * ε ^ 2 = L + ε ^ 2 := by
    field_simp [hpos.ne']

  have hbig :
    (K : ℝ) * ε ^ 2 ≥ L + ε ^ 2 := by
    simpa [hrewrite] using hmul

  have hupper := hbounded K

  have hlower' := hsum_lower K

  have hle :
    (K : ℝ) * ε ^ 2 ≤ L := by
    exact le_trans hlower' hupper

  have : (K : ℝ) * ε ^ 2 < L + ε ^ 2 := by
    linarith
  exact lt_irrefl _ (lt_of_le_of_lt hbig this)
