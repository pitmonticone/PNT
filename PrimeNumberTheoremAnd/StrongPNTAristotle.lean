import Mathlib
import PrimeNumberTheoremAnd.BorelCaratheodoryAristotle
import PrimeNumberTheoremAnd.MediumPNTAristotle

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

open ArithmeticFunction (vonMangoldt)

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "ψ" => ChebyshevPsi

--open scoped ArithmeticFunction

/-!
This upstreamed from https://github.com/math-inc/strongpnt/tree/main
-/
/-- **cauchy-formula-deriv**

Let $f$ be analytic on $|z|\leq R$. For any $z$ with $|z|\leq r$ and any $r'$
    with $0 < r < r' < R$ we have
    $$f'(z)=\frac{1}{2\pi i}\oint_{|w|=r'}\frac{f(w)}{(w-z)^2}\,dw=\frac{1}{2\pi}
    \int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$

PROVIDED SOLUTION:
This is just Cauchy's integral formula for derivatives.
-/
lemma cauchy_formula_deriv {f : ℂ → ℂ} {R r r' : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
    (r_lt_r' : r < r') (r'_lt_R : r' < R) {z : ℂ} (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  admit

/-- **DerivativeBound**

Let $R,\,M>0$ and $0 < r < r' < R$. Let $f$ be analytic on $|z|\leq R$ such that
    $f(0)=0$ and suppose $\Re f(z)\leq M$ for all $|z|\leq R$. Then we have that
    $$|f'(z)|\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}$$
    for all $|z|\leq r$.

PROVIDED SOLUTION:
By Lemma \ref{cauchy_formula_deriv} we know that
    $$f'(z)=\frac{1}{2\pi i}\oint_{|w|=r'}\frac{f(w)}{(w-z)^2}\,dw
      =\frac{1}{2\pi }\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
    Thus,
    $$
        |f'(z)|=\left|\frac{1}{2\pi}\int_0^{2\pi}
          \frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt\right|
          \leq\frac{1}{2\pi}\int_0^{2\pi}
          \left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|\,dt.
    $$
    Now applying Theorem \ref{borelCaratheodory-closedBall}, and noting that
    $r'-r\leq|r'e^{it}-z|$, we have that
    $$\left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|
      \leq\frac{2M(r')^2}{(R-r')(r'-r)^2}.$$
    Substituting this into Equation (\ref{pickupPoint1}) and evaluating the integral
    completes the proof.
-/
lemma DerivativeBound {R M r r' : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (Mpos : 0 < M)
    (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (f_zero_at_zero : f 0 = 0)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
    (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (pos_r : 0 < r) (z_in_r : z ∈ Metric.closedBall 0 r)
    (r_lt_r' : r < r') (r'_lt_R : r' < R) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  admit

/-- **BorelCaratheodoryDeriv**

Let $R,\,M>0$. Let $f$ be analytic on $|z|\leq R$ such that $f(0)=0$ and suppose
    $\Re f(z)\leq M$ for all $|z|\leq R$. Then for any $0 < r < R$,
    $$|f'(z)|\leq\frac{16MR^2}{(R-r)^3}$$
    for all $|z|\leq r$.

PROVIDED SOLUTION:
Using Lemma \ref{DerivativeBound} with $r'=(R+r)/2$, and noting that $r < R$,
    we have that
    $$|f'(z)|\leq\frac{4M(R+r)^2}{(R-r)^3}\leq\frac{16MR^2}{(R-r)^3}.$$
-/
theorem BorelCaratheodoryDeriv {M R r : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (rpos : 0 < r) (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zeroAtZero : f 0 = 0) (Mpos : 0 < M)
    (realPartBounded : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (hyp_r : r < R) (hyp_z : z ∈ Metric.closedBall 0 r)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  admit

/-- **PathIntegral**

Let $f:\mathbb{C}\to\mathbb{C}$. Define the functon $I_f:\mathbb{C}\to\mathbb{C}$ by
    $$I_f(z)=z\int_0^1f(tz)\,dt.$$
-/
noncomputable def PathIntegral (f : ℂ → ℂ) :
    ℂ → ℂ := fun c ↦ let γ : ℝ → ℂ := fun s ↦ s * c
    ∫ t in 0..1, f (γ t) * (deriv γ) t

/--
Auxilary lemmas for LogOfAnalyticFunction
-/
lemma shiftedMulCont (z : ℂ) (y : ℂ) : Continuous (fun (t : ℝ) ↦ ↑t * (z + y)) := by
  admit

lemma mulContInterval (z : ℂ) : ContinuousOn (fun (x : ℝ) ↦ ↑x * z) (Set.uIcc (0 : ℝ) 1) := by
  admit

lemma shiftedMulContInverval (z : ℂ) (y : ℂ) : ContinuousOn (fun t ↦ ↑t * (z + y)) (Set.uIcc (0 : ℝ) 1) := by
  admit

lemma PathIntegral_IBP {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R)) {z : ℂ} (hz : z ∈ Metric.ball 0 R) :
    ∫ t in (0 : ℝ)..1, (t : ℂ) * z * deriv f (t * z) = f z - ∫ t in (0 : ℝ)..1, f (t * z) := by
  admit

lemma deriv_integral_of_analytic {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R)) {z : ℂ} (hz : z ∈ Metric.ball 0 R) :
    HasDerivAt (fun z => ∫ t in (0 : ℝ)..1, f (t * z)) (∫ t in (0 : ℝ)..1, (t : ℂ) * deriv f (t * z)) z := by
  admit

theorem PathIntegral_deriv {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R)) :
    ∀ z ∈ Metric.ball 0 R, HasDerivAt (PathIntegral f) (f z) z := by
  admit

/-- **LogOfAnalyticFunction**

Let $0 < r < R$. Let $B:\overline{\mathbb{D}_R}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_R}$ with $B(z)\neq 0$ for all
    $z\in\overline{\mathbb{D}_R}$. Then there exists $J_B:\overline{\mathbb{D}_r}\to\mathbb{C}$ that
    is analytic on neighborhoods of points in $\overline{\mathbb{D}_r}$ such that
    \begin{itemize}
        \item $J_B(0)=0$
        \item $J_B'(z)=B'(z)/B(z)$
        \item $\log|B(z)|-\log|B(0)|=\Re J_B(z)$
    \end{itemize}
    for all $z\in\overline{\mathbb{D}_r}$.

PROVIDED SOLUTION:
We let $J_B(z)=I_{B'/B}(z)$. Then clearly, $J_B(0)=0$. Now note that
    \begin{align*}
        I_{B'/B}(z)=z\int_0^1(B'/B)(tz)\,dt=\int_0^z(B'/B)(u)\,du.
    \end{align*}
    Thus by the fundamental theorem of calculus we have that $J_B'(z)=B'(z)/B(z)$. Now let
    $H(z)=\exp(J_B(z))/B(z)$ and note that
    $$H'(z)=(B(z)\,J_B'(z)-B'(z))\left(\frac{\exp(J_B(z))}{(B(z))^2}\right).$$
    Thus, $H$ is constant since we know that $B(z)\,J_B'(z)-B(z)=0$ from $J_B'(z)=B'(z)/B(z)$. So
    since $H(0)=\exp(J_B(0))/B(0)=1/B(0)$ we know $H(z)=1/B(0)$ for all $z$. So we have,
    $$\frac{1}{B(0)}=\frac{\exp(J_B(z))}{B(z)}\implies\left|\frac{B(z)}{B(0)}\right|
      =\exp(\mathfrak{R}J_B(z)).$$
    Taking the logarithm of both sides completes the proof.
-/
theorem LogOfAnalyticFunction {r R : ℝ} (zero_lt_r : 0 < r) (r_lt_R : r < R)
    {B : ℂ → ℂ} (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R)) (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ),
    (AnalyticOnNhd ℂ J_B (Metric.closedBall 0 r)) ∧
    (J_B 0 = 0) ∧
    (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
    (∀ z ∈ Metric.closedBall 0 r, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  admit

/-!
\begin{definition}[SetOfZeros]
    Let $R>0$ and $f:\overline{\mathbb{D}_R}\to\mathbb{C}$. Define the set of zeros
    $\mathcal{K}_f(R)=\{\rho\in\mathbb{C}:|\rho|\leq R,\,f(\rho)=0\}$.
\end{definition}
-/



/-!
\begin{definition}[ZeroOrder]
    Let $0 < R<1$ and $f:\mathbb{C}\to\mathbb{C}$ be analtyic on neighborhoods of points in
    $\overline{\mathbb{D}_1}$. For any zero $\rho\in\mathcal{K}_f(R)$, we define $m_f(\rho)$
    as the order of the zero $\rho$ w.r.t $f$.
\end{definition}
-/



/-!
\begin{lemma}[ZeroFactorization]
    Let $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in
    $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. For all $\rho\in\mathcal{K}_f(1)$ there
    exists $h_\rho(z)$ that is analytic at $\rho$, $h_\rho(\rho)\neq 0$, and
    $f(z)=(z-\rho)^{m_f(\rho)}\,h_\rho(z)$.
\end{lemma}
-/

/-!
\begin{proof}
    Since $f$ is analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ we know
    that there exists a series expansion about $\rho$:
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n.$$
    Now if we let $m$ be the smallest number such that $a_m\neq 0$, then
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n=\sum_{m\leq n}a_n\,(z-\rho)^n
      =(z-\rho)^m\sum_{m\leq n}a_n\,(z-\rho)^{n-m}=(z-\rho)^m\,h_\rho(z).$$
    Trivially, $h_\rho(z)$ is analytic at $\rho$ (we have written down the series
    expansion); now note that
    $$h_\rho(\rho)=\sum_{m\leq n}a_n(\rho-\rho)^{n-m}=\sum_{m\leq n}a_n0^{n-m}=a_m\neq 0.$$
\end{proof}
-/



/-!
\begin{definition}[CFunction]
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. We define a
    function $C_f:\overline{\mathbb{D}_R}\to\mathbb{C}$ as follows. This function is
    constructed by dividing $f(z)$ by a polynomial whose roots are the zeros of $f$ inside
    $\overline{\mathbb{D}_r}$.
    $$C_f(z)=\begin{cases}
        \displaystyle\frac{f(z)}{\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}
          \qquad\text{for }z\not\in\mathcal{K}_f(r) \\
        \displaystyle\frac{h_z(z)}{\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
          (z-\rho)^{m_f(\rho)}}\qquad\text{for }z\in\mathcal{K}_f(r)
    \end{cases}$$
    where $h_z(z)$ comes from Lemma \ref{ZeroFactorization}.
\end{definition}
-/



/-!
\begin{definition}[BlaschkeB]
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. We define a
    function $B_f:\overline{\mathbb{D}_R}\to\mathbb{C}$ as follows.
    $$B_f(z)=C_f(z)\prod_{\rho\in\mathcal{K}_f(r)}
      \left(R-\frac{z\overline{\rho}}{R}\right)^{m_f(\rho)}$$
\end{definition}
-/



/-!
\begin{lemma}[BlaschkeOfZero]
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. Then
    $$|B_f(0)|=|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}
      \left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
\end{lemma}
-/

/-!
\begin{proof}
\uses{BlaschkeB}
    Since $f(0)\neq 0$, we know that $0\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$|B_f(0)|=|C_f(0)|\prod_{\rho\in\mathcal{K}_f(r)}R^{m_f(\rho)}
      =|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
\end{proof}
-/



/-!
\begin{lemma}[DiskBound]
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $|f(z)|\leq B$ for
    $|z|\leq R$, then $|B_f(z)|\leq B$ for $|z|\leq R$ also.
\end{lemma}
-/

/-!
\begin{proof}
\uses{BlaschkeB}
    For $|z|=R$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$|B_f(z)|=|f(z)|\prod_{\rho\in\mathcal{K}_f(r)}
      \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.$$
    But note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|
      =\frac{|R^2-z\overline{\rho}|/R}{|z-\rho|}
      =\frac{|z|\cdot|\overline{z-\rho}|/R}{|z-\rho|}=1.$$
    So we have that $|B_f(z)|=|f(z)|\leq B$ when $|z|=R$. Now by the maximum modulus
    principle, we know that the maximum of $|B_f|$ must occur on the boundary where
    $|z|=R$. Thus $|B_f(z)|\leq B$ for all $|z|\leq R$.
\end{proof}
-/



/-!
\begin{theorem}[ZerosBound]
    Let $B>1$ and $0< r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$
    for $|z|\leq R$, then
    $$\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)\leq\frac{\log B}{\log(R/r)}.$$
\end{theorem}
-/

/-!
\begin{proof}
\uses{BlaschkeB, DiskBound, BlaschkeOfZero}
    Since $f(0)=1$, by Lemma \ref{BlaschkeOfZero} we know that
    $$|B_f(0)|
      =|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}
      =\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}
      =\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{r}\right)^{m_f(\rho)}
      \leq\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}
      =|B_f(0)|\leq B$$
    whereby Lemma \ref{DiskBound} we know that $|B_f(z)|\leq B$ for all $|z|\leq R$.
    Taking the logarithm of both sides and rearranging gives the desired result.
\end{proof}
-/



/-!
\begin{definition}[JBlaschke]
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$, define
    $L_f(z)=J_{B_f}(z)$ where $J$ is from Theorem \ref{LogOfAnalyticFunction} and $B_f$
    is from Definition \ref{BlaschkeB}.
\end{definition}
-/



/-!
\begin{lemma}[BlaschkeNonZero]
    Let $0 < r < R<1$ and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$. Then $B_f(z)\neq 0$ for all
    $z\in\overline{\mathbb{D}_r}$.
\end{lemma}
-/

/-!
\begin{proof}
\uses{ZeroFactorization, BlaschkeB}
    Suppose that $z\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{h_z(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
      (z-\rho)^{m_f(\rho)}}.$$
    where $h_z(z)\neq 0$ according to Lemma \ref{ZeroFactorization}. Thus, substituting
    this into Definition \ref{BlaschkeB},
    $$
        |B_f(z)|=|h_z(z)|\cdot\left|R-\frac{|z|^2}{R}\right|^{m_f(z)}
          \prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
          \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.
    $$
    Trivially, $|h_z(z)|\neq 0$. Now note that
    $$\left|R-\frac{|z|^2}{R}\right|=0\implies|z|=R.$$
    However, this is a contradiction because $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. Similarly, note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=0\implies|z|=\frac{R^2}{|\overline{\rho}|}.$$
    However, this is also a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that
    $R < R^2/|\overline{\rho}|=|z|$, but $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. So, we know that
    $$\left|R-\frac{|z|^2}{R}\right|\neq 0\qquad\text{and}\qquad
      \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|\neq 0
      \quad\text{for all}\quad\rho\in\mathcal{K}_f(r)\setminus\{z\}.$$
    Applying this to Equation (\ref{pickupPoint2}) we have that $|B_f(z)|\neq 0$.
    So, $B_f(z)\neq 0$.

    Now suppose that $z\not\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$
        |B_f(z)|=|f(z)|\prod_{\rho\in\mathcal{K}_f(r)}
          \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.
    $$
    We know that $|f(z)|\neq 0$ since $z\not\in\mathcal{K}_f(r)$. Now note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=0\implies|z|=\frac{R^2}{|\overline{\rho}|}.$$
    However, this is a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that
    $R < R^2/|\overline{\rho}|=|z|$, but $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. So, we know that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|\neq 0
      \quad\text{for all}\quad\rho\in\mathcal{K}_f(r).$$
    Applying this to Equation (\ref{pickupPoint3}) we have that $|B_f(z)|\neq 0$.
    So, $B_f(z)\neq 0$.

    We have shown that $B_f(z)\neq 0$ for both $z\in\mathcal{K}_f(r)$ and
    $z\not\in\mathcal{K}_f(r)$, so the result follows.
\end{proof}
-/



/-!
\begin{theorem}[JBlaschkeDerivBound]
    Let $B>1$ and $0 < r' < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic
    on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$
    for all $|z|\leq R$, then for all $|z|\leq r'$
    $$|L_f'(z)|\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
\end{theorem}
-/

/-!
\begin{proof}
\uses{DiskBound, JBlaschke, LogOfAnalyticFunction, BorelCaratheodoryDeriv}
    By Lemma \ref{DiskBound} we immediately know that $|B_f(z)|\leq B$ for all $|z|\leq R$.
    Now since $L_f=J_{B_f}$ by Definition \ref{JBlaschke}, by Theorem
    \ref{LogOfAnalyticFunction} we know that
    $$L_f(0)=0\qquad\text{and}\qquad
      \Re L_f(z)=\log|B_f(z)|-\log|B_f(0)|\leq\log|B_f(z)|\leq\log B$$
    for all $|z|\leq r$. So by Theorem \ref{BorelCaratheodoryDeriv}, it follows that
    $$|L_f'(z)|\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
    for all $|z|\leq r'$.
\end{proof}
-/



/-!
\begin{theorem}[FinalBound]
    Let $B>1$ and $0 < r' < r < R' < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function
    analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and
    $|f(z)|\leq B$ for all $|z|\leq R$, then for all
    $z\in\overline{\mathbb{D}_{r'}}\setminus\mathcal{K}_f(R')$ we have
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|
      \leq\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log B.$$
\end{theorem}
-/

/-!
\begin{proof}
\uses{CFunction, BlaschkeB, JBlaschke, LogOfAnalyticFunction, ZerosBound, JBlaschkeDerivBound}
    Since $z\in\overline{\mathbb{D}_{r'}}\setminus\mathcal{K}_f(R')$ we know that
    $z\not\in\mathcal{K}_f(R')$; thus, by Definition \ref{CFunction} we know that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(R')}(z-\rho)^{m_f(\rho)}}.$$
    Substituting this into Definition \ref{BlaschkeB} we have that
    $$B_f(z)=f(z)\prod_{\rho\in\mathcal{K}_f(R')}
      \left(\frac{R-z\overline{\rho}/R}{z-\rho}\right)^{m_f(\rho)}.$$
    Taking the complex logarithm of both sides we have that
    $$\mathrm{Log}\,B_f(z)=\mathrm{Log}\,f(z)
      +\sum_{\rho\in\mathcal{K}_f(R')}m_f(\rho)\,\mathrm{Log}(R-z\overline{\rho}/R)
      -\sum_{\rho\in\mathcal{K}_f(R')}m_f(\rho)\,\mathrm{Log}(z-\rho).$$
    Taking the derivative of both sides we have that
    $$\frac{B_f'}{B_f}(z)=\frac{f'}{f}(z)
      +\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-R^2/\overline{\rho}}
      -\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}.$$
    By Definition \ref{JBlaschke} and Theorem \ref{LogOfAnalyticFunction},
    since $L_f(z)=J_{B_f}(z)$ we have $L_f'(z)=J'_{B_f}(z)=(B_f'/B_f)(z)$. Thus,
    $$\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}
      =L_f'(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-R^2/\overline{\rho}}.$$
    Now since $z\in\overline{\mathbb{D}_{R'}}$ and $\rho\in\mathcal{K}_f(R')$, we know that
    $R^2/R'-R'\leq|z-R^2/\overline{\rho}|$. Thus by the triangle inequality we have
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|
      \leq|L_f'(z)|+\left(\frac{1}{R^2/R'-R'}\right)\sum_{\rho\in\mathcal{K}_f(R')}m_f(\rho).$$
    Now by Theorem \ref{ZerosBound} and \ref{JBlaschkeDerivBound} we get our desired result
    with a little algebraic manipulation.
\end{proof}
-/



/-!
\begin{theorem}[ZetaFixedLowerBound]
    For all $t\in\mathbb{R}$ one has
    $$|\zeta(3/2+it)|\geq\frac{\zeta(3)}{\zeta(3/2)}.$$
\end{theorem}
-/

/-!
\begin{proof}
    From the Euler product expansion of $\zeta$, we have that for $\Re s>1$
    $$\zeta(s)=\prod_p\frac{1}{1-p^{-s}}.$$
    Thus, we have that
    $$\frac{\zeta(2s)}{\zeta(s)}=\prod_p\frac{1-p^{-s}}{1-p^{-2s}}=\prod_p\frac{1}{1+p^{-s}}.$$
    Now note that $|1-p^{-(3/2+it)}|\leq 1+|p^{-(3/2+it)}|=1+p^{-3/2}$. Thus,
    $$|\zeta(3/2+it)|=\prod_p\frac{1}{|1-p^{-(3/2+it)}|}
      \geq\prod_p\frac{1}{1+p^{-3/2}}=\frac{\zeta(3)}{\zeta(3/2)}$$
    for all $t\in\mathbb{R}$ as desired.
\end{proof}
-/



/-!
\begin{lemma}[ZetaAltFormula]
    Let
    $$\zeta_0(s)=1+\frac{1}{s-1}-s\int_1^\infty\{x\}\,x^{-s}\,\frac{dx}{x}.$$
    We have that $\zeta(s)=\zeta_0(s)$ for $\sigma>1$.
\end{lemma}
-/

/-!
\begin{proof}
    Note that for $\sigma>1$ we have
    $$\zeta(s)=\sum_{n=1}^\infty\frac{1}{n^s}
      =\sum_{n=1}^\infty\frac{n}{n^s}-\sum_{n=1}^\infty\frac{n-1}{n^s}
      =\sum_{n=1}^\infty\frac{n}{n^s}-\sum_{n=0}^\infty\frac{n}{(n+1)^s}
      =\sum_{n=1}^\infty\frac{n}{n^s}-\sum_{n=1}^\infty\frac{n}{(n+1)^s}.$$
    Thus
    $$\zeta(s)=\sum_{n=1}^\infty n\,(n^{-s}-(n+1)^{-s}).$$
    Now we note that
    $$s\int_n^{n+1}x^{-s}\,\frac{dx}{x}
      =s\left(-\frac{1}{s}\,x^{-s}\right)_n^{n+1}=n^{-s}-(n+1)^{-s}.$$
    So, substituting this we have
    $$\zeta(s)=\sum_{n=1}^\infty n\,(n^{-s}-(n+1)^{-s})
      =s\sum_{n=1}^\infty n\int_n^{n+1}x^{-s}\,\frac{dx}{x}
      =s\int_1^\infty\lfloor x\rfloor\,x^{-s}\,\frac{dx}{x}.$$
    But noting that $\lfloor x\rfloor =x-\{x\}$ we have that
    $$\zeta(s)=s\int_1^\infty\lfloor x\rfloor\,x^{-s}\,\frac{dx}{x}
      =s\int_1^\infty x^{-s}\,dx-s\int_1^\infty \{x\}\,x^{-s}\,\frac{dx}{x}.$$
    Evaluating the first integral completes the result.
\end{proof}
-/



/-!
\begin{lemma}[ZetaAltFormulaAnalytic]
    We have that $\zeta_0(s)$ is analytic for all $s\in S$ where
    $S=\{s\in\mathbb{C}:\Re s>0,\,s\neq 1\}$.
\end{lemma}
-/

/-!
\begin{proof}
    Note that we have
    $$\left|\int_1^\infty\{x\}\,x^{-s}\,\frac{dx}{x}\right|
      \leq\int_1^\infty|\{x\}\,x^{-s-1}|\,dx
      \leq\int_1^\infty x^{-\sigma-1}\,dx=\frac{1}{\sigma}.$$
    So this integral converges uniformly on compact subsets of $S$, which tells us that
    it is analytic on $S$. So it immediately follows that $\zeta_0(s)$ is analytic on $S$
    as well, since $S$ avoids the pole at $s=1$ coming from the $(s-1)^{-1}$ term.
\end{proof}
-/



/-!
\begin{lemma}[ZetaExtend]
    We have that
    $$\zeta(s)=1+\frac{1}{s-1}-s\int_1^\infty\{x\}\,x^{-s}\,\frac{dx}{x}$$
    for all $s\in S$.
\end{lemma}
-/

/-!
\begin{proof}
    This is an immediate consequence of the identity theorem.
\end{proof}
-/



/-!
\begin{theorem}[GlobalBound]
    For all $s\in\mathbb{C}$ with $|s|\leq 1$ and $t\in\mathbb{R}$ with $|t|\geq 2$, we have that
    $$|\zeta(s+3/2+it)|\leq 7+2\,|t|.$$
\end{theorem}
-/

/-!
\begin{proof}
\uses{ZetaExtend}
    For the sake of clearer proof writing let $z=s+3/2+it$. Since $|s|\leq 1$ we know that
    $1/2\leq\mathfrak{R}z$; additionally, as $|t|\geq 2$, we know $1\leq|\mathfrak{I}z|$.
    So, $z\in S$. Thus, from Lemma \ref{ZetaExtend} we know that
    $$|\zeta(z)|\leq 1+\frac{1}{|z-1|}
      +|z|\cdot\left|\int_1^\infty\{x\}\,x^{-z}\,\frac{dx}{x}\right|$$
    by applying the triangle inequality. Now note that $|z-1|\geq 1$. Likewise,
    $$|z|\cdot\left|\int_1^\infty\{x\}\,x^{-z}\,\frac{dx}{x}\right|
      \leq|z|\int_1^\infty|\{x\}\,x^{-z-1}|\,dx
      \leq|z|\int_1^\infty x^{-\Re z-1}\,dx=\frac{|z|}{\Re z}\leq 2\,|z|.$$
    Thus we have that,
    $$|\zeta(s+3/2+it)|=|\zeta(z)|\leq 1+1+2\,|z|=2+2\,|s+3/2+it|
      \leq2+2\,|s|+3+2\,|it|\leq 7+2\,|t|.$$
\end{proof}
-/



/-!
\begin{theorem}[LogDerivZetaFinalBound]
    Let $t\in\mathbb{R}$ with $|t|\geq 2$ and $0 < r' < r < R' < R<1$. If
    $f(z)=\zeta(z+3/2+it)$, then for all
    $z\in\overline{\mathbb{D}_{r'}}\setminus\mathcal{K}_f(R')$ we have that
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|
      \ll\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log|t|.$$
\end{theorem}
-/

/-!
\begin{proof}
\uses{ZetaFixedLowerBound, GlobalBound, FinalBound}
    Let $g(z)=\zeta(z+3/2+it)/\zeta(3/2+it)$. Note that $g(0)=1$ and for $|z|\leq R$
    $$|g(z)|=\frac{|\zeta(z+3/2+it)|}{|\zeta(3/2+it)|}
      \leq\frac{\zeta(3/2)}{\zeta(3)}\cdot(7+2\,|t|)\leq\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\,|t|$$
    by Theorems \ref{ZetaFixedLowerBound} and \ref{GlobalBound}. Thus by Theorem
    \ref{FinalBound} we have that
    $$\left|\frac{g'}{g}(z)-\sum_{\rho\in\mathcal{K}_g(R')}\frac{m_g(\rho)}{z-\rho}\right|
      \leq\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)
      \left(\log|t|+\log\left(\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\right)\right).$$
    Now note that $f'/f=g'/g$, $\mathcal{K}_f(R')=\mathcal{K}_g(R')$, and
    $m_g(\rho)=m_f(\rho)$ for all $\rho\in\mathcal{K}_f(R')$. Thus we have that,
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|
      \ll\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log|t|$$
    where the implied constant $C$ is taken to be
    $$C\geq 1+\frac{\log((13\,\zeta(3/2))/(3\,\zeta(3)))}{\log 2}.$$
\end{proof}
-/



/-!
\begin{definition}[ZeroWindows]
    Let $\mathcal{Z}_t=\{\rho\in\mathbb{C}:\zeta(\rho)=0,\,|\rho-(3/2+it)|\leq 5/6\}$.
\end{definition}
-/



/-!
\begin{lemma}[SumBoundI]
    For all $\delta\in (0,1)$ and $t\in\mathbb{R}$ with $|t|\geq 2$ we have
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|\ll\log|t|.$$
\end{lemma}
-/

/-!
\begin{proof}
\uses{LogDerivZetaFinalBound}
    We apply Theorem \ref{LogDerivZetaFinalBound} where $r'=2/3$, $r=3/4$, $R'=5/6$, and
    $R=8/9$. Thus, for all $z\in\overline{\mathbb{D}_{2/3}}\setminus\mathcal{K}_f(5/6)$
    we have that
    $$\left|\frac{\zeta'}{\zeta}(z+3/2+it)
      -\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{z-\rho}\right|\ll\log|t|$$
    where $f(z)=\zeta(z+3/2+it)$ for $t\in\mathbb{R}$ with $|t|\geq 3$. Now if we let
    $z=-1/2+\delta$, then $z\in(-1/2,1/2)\subseteq\overline{\mathbb{D}_{2/3}}$.
    Additionally, $f(z)=\zeta(1+\delta+it)$, where $1+\delta+it$ lies in the zero-free
    region where $\sigma>1$. Thus, $z\not\in\mathcal{K}_f(5/6)$. So,
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{-1/2+\delta-\rho}\right|
      \ll\log|t|.$$
    But now note that if $\rho\in\mathcal{K}_f(5/6)$, then $\zeta(\rho+3/2+it)=0$ and
    $|\rho|\leq 5/6$. Thus, $\rho+3/2+it\in\mathcal{Z}_t$. Additionally, note that
    $m_f(\rho)=m_\zeta(\rho+3/2+it)$. So changing variables using these facts gives us
    that
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|
      \ll\log|t|.$$
\end{proof}
-/



/-!
\begin{lemma}[ShiftTwoBound]
    For all $\delta\in (0,1)$ and $t\in\mathbb{R}$ with $|t|\geq 2$ we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)\ll\log|t|.$$
\end{lemma}
-/

/-!
\begin{proof}
\uses{SumBoundI}
    Note that, for $\rho\in\mathcal{Z}_{2t}$
    \begin{align*}
        \Re \left(\frac{1}{1+\delta+2it-\rho}\right)
          &=\Re \left(\frac{1+\delta-2it-\overline{\rho}}
            {(1+\delta+2it-\rho)(1+\delta-2it-\overline{\rho})}\right) \\
          &=\frac{\Re (1+\delta-2it-\overline{\rho})}{|1+\delta+2it-\rho|^2}
            =\frac{1+\delta-\Re \rho}{(1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2}.
    \end{align*}
    Now since $\rho\in\mathcal{Z}_{2t}$, we have that $|\rho-(3/2+2it)|\leq 5/6$. So,
    we have $\Re \rho\in(2/3,7/3)$ and $\mathfrak{I}\rho\in(2t-5/6,2t+5/6)$. Thus, we
    have that
    $$1/3<1+\delta-\Re \rho\qquad\text{and}\qquad
      (1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2<16/9+25/36=89/36.$$
    Which implies that
    $$
        0\leq\frac{12}{89}
          <\frac{1+\delta-\Re \rho}{(1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2}
          =\Re \left(\frac{1}{1+\delta+2it-\rho}\right).
    $$
    Note that, from Lemma \ref{SumBoundI}, we have
    $$\sum_{\rho\in\mathcal{Z}_{2t}}m_\zeta(\rho)\,
      \Re \left(\frac{1}{1+\delta+2it-\rho}\right)
      -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)
      \leq\left|\frac{\zeta'}{\zeta}(1+\delta+2it)
      -\sum_{\rho\in\mathcal{Z}_{2t}}\frac{m_\zeta(\rho)}{1+\delta+2it-\rho}\right|
      \ll\log|2t|.$$
    Since $m_\zeta(\rho)\geq 0$ for all $\rho\in\mathcal{Z}_{2t}$, the inequality from
    Equation (\ref{pickupPoint4}) tells us that by subtracting the sum from both sides
    we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)\ll\log|2t|.$$
    Noting that $\log|2t|=\log(2)+\log|t|\leq2\log|t|$ completes the proof.
\end{proof}
-/



/-!
\begin{lemma}[ShiftOneBound]
    There exists $C>0$ such that for all $\delta\in(0,1)$ and $t\in\mathbb{R}$ with
    $|t|\geq 3$; if $\zeta(\rho)=0$ with $\rho=\sigma+it$, then
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
      \leq -\frac{1}{1+\delta-\sigma}+C\log|t|.$$
\end{lemma}
-/

/-!
\begin{proof}
\uses{SumBoundI}
    Note that for $\rho'\in\mathcal{Z}_t$
    \begin{align*}
        \Re \left(\frac{1}{1+\delta+it-\rho'}\right)
          &=\Re \left(\frac{1+\delta-it-\overline{\rho'}}
            {(1+\delta+it-\rho')(1+\delta-it-\overline{\rho'})}\right) \\
          &=\frac{\Re (1+\delta-it-\overline{\rho'})}{|1+\delta+it-\rho'|^2}
            =\frac{1+\delta-\Re \rho'}{(1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2}.
    \end{align*}
    Now since $\rho'\in\mathcal{Z}_t$, we have that $|\rho-(3/2+it)|\leq 5/6$. So, we
    have $\Re \rho'\in(2/3,7/3)$ and $\mathfrak{I}\rho'\in(t-5/6,t+5/6)$. Thus we have
    that
    $$1/3<1+\delta-\Re \rho'\qquad\text{and}\qquad
      (1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2<16/9+25/36=89/36.$$
    Which implies that
    $$
        0\leq\frac{12}{89}
          <\frac{1+\delta-\Re \rho'}{(1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2}
          =\Re \left(\frac{1}{1+\delta+it-\rho'}\right).
    $$
    Note that, from Lemma \ref{SumBoundI}, we have
    $$\sum_{\rho\in\mathcal{Z}_t}m_\zeta(\rho)\,
      \Re \left(\frac{1}{1+\delta+it-\rho}\right)
      -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
      \leq\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|
      \ll\log|t|.$$
    Since $m_\zeta(\rho)\geq 0$ for all $\rho'\in\mathcal{Z}_t$, the inequality from
    Equation (\ref{pickupPoint5}) tells us that by subtracting the sum over all
    $\rho'\in\mathcal{Z}_t\setminus\{\rho\}$ from both sides we have
    $$\frac{m_\zeta(\rho)}{\Re (1+\delta+it-\rho)}
      -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)\ll\log|t|.$$
    But of course we have that $\Re (1+\delta+it-\rho)=1+\delta-\sigma$. So subtracting
    this term from both sides and recalling the implied constant we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
      \leq -\frac{m_\zeta(\rho)}{1+\delta-\sigma}+C\log|t|.$$
    We have that $\sigma\leq 1$ since $\zeta$ is zero free on the right half plane
    $\sigma>1$. Thus $0<1+\delta-\sigma$. Noting this in combination with the fact that
    $1\leq m_\zeta(\rho)$ completes the proof.
\end{proof}
-/



/-!
\begin{lemma}[ShiftZeroBound]
    For all $\delta\in(0,1)$ we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)\leq\frac{1}{\delta}+O(1).$$
\end{lemma}
-/

/-!
\begin{proof}
\uses{riemannZetaLogDerivResidue}
    From Theorem \ref{riemannZetaLogDerivResidue} we know that
    $$-\frac{\zeta'}{\zeta}(s)=\frac{1}{s-1}+O(1).$$
    Changing variables $s\mapsto 1+\delta$ and applying the triangle inequality we have that
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)\leq\left|
      -\frac{\zeta'}{\zeta}(1+\delta)\right|\leq\frac{1}{\delta}+O(1).$$
\end{proof}
-/



/-!
\begin{lemma}[ThreeFourOneTrigIdentity]
    We have that
    $$0\leq 3+4\cos\theta+\cos2\theta$$
    for all $\theta\in\mathbb{R}$.
\end{lemma}
-/

/-!
\begin{proof}
    We know that $\cos(2\theta)=2\cos^2\theta-1$, thus
    $$3+4\cos\theta+\cos2\theta=2+4\cos\theta+2\cos^2\theta=2\,(1+\cos\theta)^2.$$
    Noting that $0\leq 1+\cos\theta$ completes the proof.
\end{proof}
-/
/-- **ZeroInequality**

There exists a constant $0 < E<1$ such that for all $\rho=\sigma+it$ with $\zeta(\rho)=0$
    and $|t|\geq 2$, one has
    $$\sigma\leq 1-\frac{E}{\log|t|}.$$

PROVIDED SOLUTION:
From Theorem \ref{LogDerivativeDirichlet} when $\Re s>1$ we have
    $$-\frac{\zeta'}{\zeta}(s)=\sum_{1\leq n}\frac{\Lambda(n)}{n^s}.$$
    Thus,
    $$-3\,\frac{\zeta'}{\zeta}(1+\delta)
        -4\,\frac{\zeta'}{\zeta}(1+\delta+it)
        -\frac{\zeta'}{\zeta}(1+\delta+2it)
        =\sum_{1\leq n}\Lambda(n)\,n^{-(1+\delta)}\left(3+4n^{-it}+n^{-2it}\right).$$
    Now applying Euler's identity
    \begin{align*}
        -3\,\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)&
            -4\,\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
            -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right) \\
        &\qquad\qquad\qquad=\sum_{1\leq n}\Lambda(n)\,n^{-(1+\delta)}
            \left(3+4\cos(-it\log n)+\cos(-2it\log n)\right)
    \end{align*}
    By Lemma \ref{ThreeFourOneTrigIdentity} we know that the series on the right hand side
    is bounded below by $0$, and by Lemmas \ref{ShiftTwoBound}, \ref{ShiftOneBound},
    and \ref{ShiftZeroBound} we have an upper bound on the left hand side. So,
    $$0\leq\frac{3}{\delta}+3A-\frac{4}{1+\delta-\sigma}+4B\log|t|+C\log|t|$$
    where $A$, $B$, and $C$ are the implied constants coming from Lemmas
    \ref{ShiftZeroBound}, \ref{ShiftOneBound}, and \ref{ShiftTwoBound} respectively.
    By choosing $D\geq 3A/\log 2+4B+C$ we have
    $$\frac{4}{1+\delta-\sigma}\leq\frac{3}{\delta}+D\log|t|$$
    by some manipulation. Now if we choose $\delta=(2D\log|t|)^{-1}$ then we have
    $$\frac{4}{1-\sigma+1/(2D\log|t|)}\leq7D\log|t|.$$
    So with some manipulation we have that
    $$\sigma\leq 1-\frac{1}{14D\log|t|}.$$
    This is exactly the desired result with the constant $E=(14D)^{-1}$
-/
theorem ZeroInequality : ∃ (E : ℝ) (EinIoo : E ∈ Ioo (0 : ℝ) 1),
    ∀ (ρ : ℂ) (σ t : ℝ),
    ζ ρ = 0 →
        σ = ρ.re →
            t = ρ.im →
                |t| ≥ 2 →
                    σ ≤ 1 - E / log |t| := by
    sorry




noncomputable def E : ℝ := ZeroInequality.choose
lemma EinIoo : E ∈ Ioo (0 : ℝ) 1 := by
  admit

theorem ZeroInequalitySpecialized : ∀ (ρ : ℂ) (σ t : ℝ),
    ζ ρ = 0 →
        σ = ρ.re →
            t = ρ.im →
                |t| ≥ 2 →
                    σ ≤ 1 - E / log |t| := by
  admit

/-- **DeltaT**

Let $\delta_t=E/\log|t|$ where $E$ is the constant coming from Theorem \ref{ZeroInequality}.
-/
noncomputable def DeltaT (t : ℝ) : ℝ := E / log |t|
/-- **DeltaRange**

For all $t\in\mathbb{R}$ with $|t|\geq 2$ we have that $$\delta_t<1/14.$$

PROVIDED SOLUTION:
Note that $\delta_t=E/\log|t|$ where $E$ is the implied constant from
    Lemma \ref{ZeroInequality}. But we know that $E=(14D)^{-1}$ where $D\geq 3A/\log 2+4B+C$
    where $A$, $B$, and $C$ are the constants coming from
    Lemmas \ref{ShiftZeroBound}, \ref{ShiftOneBound}, and \ref{ShiftTwoBound} respectively. Thus,
    $$E\leq\frac{1}{14\,(3A/\log 2+4B+C)}.$$
    But note that $A\geq 0$ and $B\geq 0$ by Lemmas \ref{ShiftZeroBound} and \ref{ShiftOneBound}
    respectively. However, we have that
    $$C\geq 2+\frac{2\log((13\,\zeta(3/2))/(3\,\zeta(3)))}{\log 2}$$
    by Theorem \ref{LogDerivZetaFinalBound} with Lemmas \ref{SumBoundI} and \ref{ShiftTwoBound}.
    So, by a very lazy estimate we have $C\geq 2$ and $E\leq 1/28$. Thus,
    $$\delta_t=\frac{E}{\log|t|}\leq\frac{1}{28\,\log2}<\frac{1}{14}.$$
-/
lemma DeltaRange : ∀ (t : ℝ),
    |t| ≥ 2 →
        DeltaT t < (1 : ℝ) / 14 := by
    sorry




/-!
\begin{lemma}[SumBoundII]
    For all $t\in\mathbb{R}$ with $|t|\geq 2$ and $z=\sigma+it$
    where $1-\delta_t/3\leq\sigma\leq 3/2$, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{z-\rho}\right|\ll\log|t|.$$
\end{lemma}
-/

/-!
\begin{proof}
\uses{DeltaRange, LogDerivZetaFinalBound, ZeroInequality}
    By Lemma \ref{DeltaRange} we have that
    $$-11/21<-1/2-\delta_t/3\leq\sigma-3/2\leq0.$$
    We apply Theorem \ref{LogDerivZetaFinalBound} where $r'=2/3$, $r=3/4$, $R'=5/6$, and $R=8/9$.
    Thus for all $z\in\overline{\mathbb{D}_{2/3}}\setminus\mathcal{K}_f(5/6)$ we have that
    $$\left|\frac{\zeta'}{\zeta}(z+3/2+it)
      -\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{z-\rho}\right|\ll\log|t|$$
    where $f(z)=\zeta(z+3/2+it)$ for $t\in\mathbb{R}$ with $|t|\geq 3$.
    Now if we let $z=\sigma-3/2$, then $z\in(-11/21,0)\subseteq\overline{\mathbb{D}_{2/3}}$.
    Additionally, $f(z)=\zeta(\sigma+it)$, where $\sigma+it$ lies in the zero free region given by
    Lemma \ref{ZeroInequality} since $\sigma\geq 1-\delta_t/3\geq 1-\delta_t$.
    Thus, $z\not\in\mathcal{K}_f(5/6)$. So,
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)
      -\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{\sigma-3/2-\rho}\right|\ll\log|t|.$$
    But now note that if $\rho\in\mathcal{K}_f(5/6)$, then $\zeta(\rho+3/2+it)=0$
    and $|\rho|\leq 5/6$. Additionally, note that $m_f(\rho)=m_\zeta(\rho+3/2+it)$.
    So changing variables using these facts gives us that
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{\sigma+it-\rho}\right|\ll\log|t|.$$
\end{proof}
-/



/-!
\begin{lemma}[GapSize]
   Let $t\in\mathbb{R}$ with $|t|\geq 3$ and $z=\sigma+it$ where $1-\delta_t/3\leq\sigma\leq 3/2$.
   Additionally, let $\rho\in\mathcal{Z}_t$. Then we have that
   $$|z-\rho|\geq\delta_t/6.$$
\end{lemma}
-/

/-!
\begin{proof}
\uses{ZeroInequality}
    Let $\rho=\sigma'+it'$ and note that since $\rho\in\mathcal{Z}_t$, we have $t'\in(t-5/6,t+5/6)$.
    Thus, if $t>1$ we have
    $$\log|t'|\leq\log|t+5/6|\leq\log|2t|=\log 2+\log|t|\leq 2\log|t|.$$
    And otherwise if $t<-1$ we have
    $$\log|t'|\leq\log|t-5/6|\leq\log|2t|=\log 2+\log|t|\leq 2\log|t|.$$
    So by taking reciprocals and multiplying through by a constant we have
    that $\delta_t\leq2\delta_{t'}$. Now note that since $\rho\in\mathcal{Z}_t$
    we know that $\sigma'\leq 1-\delta_{t'}$ by Theorem \ref{ZeroInequality}
    (here we use the fact that $|t|\geq 3$ to give us that $|t'|\geq 2$). Thus,
    $$\delta_t/6\leq\delta_{t'}-\delta_t/3
      =1-\delta_t/3-(1-\delta_{t'})\leq\sigma-\sigma'\leq|z-\rho|.$$
\end{proof}
-/
/-- **LogDerivZetaUniformLogSquaredBoundStrip**

There exists a constant $F\in(0,1/2)$ such that
    for all $t\in\mathbb{R}$ with $|t|\geq 3$ one has
    $$1-\frac{F}{\log|t|}\leq\sigma\leq 3/2
      \implies\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|\ll\log^2|t|$$
    where the implied constant is uniform in $\sigma$.

PROVIDED SOLUTION:
Take $F=E/3$ where $E$ comes from Theorem \ref{ZeroInequality}.
    Then we have that $\sigma\geq 1-\delta_t/3$. So, we apply Lemma \ref{SumBoundII},
    which gives us that
    $$\left|\frac{\zeta'}{\zeta}(z)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{z-\rho}\right|\ll\log|t|.$$
    Using the reverse triangle inequality and rearranging, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|
      \leq\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{|z-\rho|}+C\,\log|t|$$
    where $C$ is the implied constant in Lemma \ref{SumBoundII}.
    Now applying Lemma \ref{GapSize} we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|
      \leq\frac{6}{\delta_t}\sum_{\rho\in\mathcal{Z}_t}m_\zeta(\rho)+C\,\log|t|.$$
    Now let $f(z)=\zeta(z+3/2+it)/\zeta(3/2+it)$ with $\rho=\rho'+3/2+it$.
    Then if $\rho\in\mathcal{Z}_t$ we have that
    $$0=\zeta(\rho)=\zeta(\rho'+3/2+it)=f(\rho')$$
    with the same multiplicity of zero, that is $m_\zeta(\rho)=m_f(\rho')$.
    And also if $\rho\in\mathcal{Z}_t$ then
    $$5/6\geq|\rho-(3/2+it)|=|\rho'|.$$
    Thus we change variables to have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|
      \leq\frac{6}{\delta_t}\sum_{\rho'\in\mathcal{K}_f(5/6)}m_f(\rho')+C\,\log|t|.$$
    Now note that $f(0)=1$ and for $|z|\leq 8/9$ we have
    $$|f(z)|=\frac{|\zeta(z+3/2+it)|}{|\zeta(3/2+it)|}
      \leq\frac{\zeta(3/2)}{\zeta(3)}\cdot(7+2\,|t|)\leq\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\,|t|$$
    by Theorems \ref{ZetaFixedLowerBound} and \ref{GlobalBound}.
    Thus by Theorem \ref{ZerosBound} we have that
    $$\sum_{\rho'\in\mathcal{K}_f(5/6)}m_f(\rho')
      \leq\frac{\log|t|+\log(13\,\zeta(3/2)/(3\,\zeta(3)))}{\log((8/9)/(5/6))}\leq D\log|t|$$
    where $D$ is taken to be sufficiently large.
    Recall, by definition that, $\delta_t=E/\log|t|$ with $E$ coming from
    Theorem \ref{ZeroInequality}. By using this fact and the above, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|\ll\log^2|t|+\log|t|$$
    where the implied constant is taken to be bigger than $\max(6D/E,C)$.
    We know that the RHS is bounded above by $\ll\log^2|t|$; so the result follows.
-/
lemma LogDerivZetaUniformLogSquaredBoundStrip : ∃ (F : ℝ) (Fequ : F = E / 3) (C : ℝ)
    (Cnonneg : 0 ≤ C), ∀ (σ t : ℝ),
    3 ≤ |t| →
        σ ∈ Set.Icc (1 - F / Real.log |t|) (3 / 2) →
            ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ 2 := by
    use E / 3
    refine exists_prop.mpr ?_
    constructor
    ·   rfl
    ·   sorry




noncomputable def F : ℝ := LogDerivZetaUniformLogSquaredBoundStrip.choose
lemma Fequ : F = E / 3 := by
  admit

lemma LogDerivZetaUniformLogSquaredBoundStripSpec : ∃ (C : ℝ) (_ : 0 ≤ C),
    ∀ (σ t : ℝ),
    3 ≤ |t| →
        σ ∈ Set.Icc (1 - F / Real.log |t|) (3 / 2) →
            ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ 2 := by
  admit

lemma FLogTtoDeltaT : ∀ (t : ℝ),
    DeltaT t / 3 = F / Real.log |t| := by
  admit

/-- The logarithmic derivative of the Riemann zeta function is bounded in the half-plane
`Re(s) >= 3/2`. -/
lemma LogDerivZetaBdd_of_Re_ge_three_halves :
    ∃ C, ∀ (s : ℂ), 3/2 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ C := by
  admit

/-- **LogDerivZetaUniformLogSquaredBound**

There exists a constant $F\in(0,1/2)$ such that for all $t\in\mathbb{R}$ with $|t|\geq 3$ one has
    $$1-\frac{F}{\log|t|}\leq\sigma\implies\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|\ll\log^2|t|$$
    where the implied constant is uniform in $\sigma$.

PROVIDED SOLUTION:
Note that
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|
      =\sum_{1\leq n}\frac{\Lambda(n)}{|n^{\sigma+it}|}=\sum_{1\leq n}\frac{\Lambda(n)}{n^\sigma}
      =-\frac{\zeta'}{\zeta}(\sigma)\leq\left|\frac{\zeta'}{\zeta}(\sigma)\right|.$$
    From Theorem \ref{riemannZetaLogDerivResidue}, and applying the triangle inequality we know that
    $$\left|\frac{\zeta'}{\zeta}(s)\right|\leq\frac{1}{|s-1|}+C.$$
    where $C>0$ is some constant. Thus, for $\sigma\geq 3/2$ we have that
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|
      \leq\left|\frac{\zeta'}{\zeta}(\sigma)\right|
      \leq\frac{1}{\sigma-1}+C\leq 2+C\ll 1\ll\log^2|t|.$$
    Putting this together with Lemma \ref{LogDerivZetaUniformLogSquaredBoundStrip}
    completes the proof.
-/
theorem LogDerivZetaUniformLogSquaredBound : ∃ (C : ℝ) (_Cnonneg : 0 ≤ C),
    ∀ (σ t : ℝ), 3 < |t| → σ ∈ Set.Ici (1 - F / Real.log |t|) →
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by
  admit

/-- **LogDerivZetaLogSquaredBoundSmallt**

For $T>0$ and $\sigma'=1-\delta_T/3=1-F/\log T$, if $|t|\leq T$ then we have that
    $$\left|\frac{\zeta'}{\zeta}(\sigma'+it)\right|\ll\log^2(2+T).$$

PROVIDED SOLUTION:
Note that if $|t|\geq 3$ then from Theorem \ref{LogDerivZetaUniformLogSquaredBound} we have that
    $$\left|\frac{\zeta'}{\zeta}(\sigma'+it)\right|\ll\log^2|t|\leq\log^2T\leq\log^2(2+T).$$
    Otherwise, if $|t|\leq 3$, then from Theorem \ref{riemannZetaLogDerivResidue}
    and applying the triangle inequality we know
    $$\left|\frac{\zeta'}{\zeta}(\sigma'+it)\right|
      \leq\frac{1}{|(\sigma'-1)+it|}+C\leq\frac{\log T}{F}+C$$
    where $C\geq 0$. Thus, we have that
    $$\left|\frac{\zeta'}{\zeta}(\sigma'+it)\right|
      \leq\left(\frac{\log T}{F\,\log 2}+\frac{C}{\log 2}\right)\,\log(2+|t|)
      \leq\left(\frac{\log(2+T)}{F\,\log 2}+\frac{C}{\log 2}\right)\log(2+T)
      \ll\log^2(2+T).$$
-/
theorem LogDerivZetaLogSquaredBoundSmallt : ∃ (C : ℝ) (Cnonneg : C ≥ 0),
    ∀ (σ t T : ℝ) (Tpos: T > 0),
    |t| ≤ T →
        σ = 1 - F / Real.log T →
            ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log (2 + T) ^ 2 := by
    sorry




/-!
From here out we closely follow our previous proof of the Medium PNT and we modify it
using our new estimate in Theorem \ref{LogDerivZetaUniformLogSquaredBound}.
Recall Definition \ref{SmoothedChebyshev}; for fixed $\varepsilon>0$
and a bump function $\nu$ supported on $[1/2,2]$ we have
$$\psi_\varepsilon(X)
  =\frac{1}{2\pi i}\int_{(\sigma)}\left(-\frac{\zeta'}{\zeta}(s)\right)
  \,\mathcal{M}(\tilde{1}_\varepsilon)(s)\,X^s\,ds$$
where $\sigma=1+1/\log X$. Let $T>3$ be a large constant to be chosen later,
and we take $\sigma'=1-\delta_T/3=1-F/\log T$ with $F$ coming from
Theorem \ref{LogDerivZetaUniformLogSquaredBound}. We integrate along the $\sigma$ vertical line,
and we pull contours  accumulating the pole at $s=1$ when we integrate along the curves
\begin{itemize}
    \item $I_1$: $\sigma-i\infty$ to $\sigma-iT$
    \item $I_2$: $\sigma'-iT$ to $\sigma-iT$
    \item $I_3$: $\sigma'-iT$ to $\sigma'+iT$
    \item $I_4$: $\sigma'+iT$ to $\sigma+iT$
    \item $I_5$: $\sigma+iT$ to $\sigma+i\infty$.
\end{itemize}
-/
/-- **I1New**

Let
    $$I_1(\nu,\varepsilon,X,T)=
      \frac{1}{2\pi i}\int_{-\infty}^{-T}\left(-\frac{\zeta'}{\zeta}(\sigma+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma+it)\,X^{\sigma+it}\,dt.$$
-/
noncomputable def I1New (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))
/-- **I5New**

Let
    $$I_5(\nu,\varepsilon,X,T)=
      \frac{1}{2\pi i}\int_T^\infty\left(-\frac{\zeta'}{\zeta}(\sigma+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma+it)\,X^{\sigma+it}\,dt.$$
-/
noncomputable def I5New (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

lemma IntegralLogSqOverTSqBound : ∃ C > 0, ∀ T, 3 < T →
  ∫ t in Set.Ici T, (Real.log t)^2 / t^2 ≤ C / Real.sqrt T := by
  admit

lemma NormXPowS {X : ℝ} (X_gt_one : 1 < X) {s : ℂ} (hs : s.re = 1 + (Real.log X)⁻¹) :
    ‖(X : ℂ) ^ s‖ = X * Real.exp 1 := by
  admit

lemma LogDerivZetaBoundForI1 : ∃ C > 0, ∀ {X T : ℝ} (_Xgt3 : 3 < X) (_Tgt3 : 3 < T)
    (t : ℝ) (_ht : t ≤ -T),
    let σ := 1 + (Real.log X)⁻¹
    ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * (Real.log (-t))^2 := by
  admit

lemma I1NewIntegrandBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ C > 0, ∀ {ε X T : ℝ} (_εinIoo : ε ∈ Set.Ioo 0 1) (_Xgt3 : 3 < X) (_Tgt3 : 3 < T)
    (t : ℝ) (_ht : t ≤ -T),
    ‖SmoothedChebyshevIntegrand SmoothingF ε X (1 + (Real.log X)⁻¹ + t * I)‖ ≤
    C * (X / ε) * (Real.log (-t))^2 / (-t)^2 := by
  admit

/-- **I1NewBound**

We have that
    $$|I_1(\nu,\varepsilon,X,T)|\ll\frac{X}{\varepsilon\sqrt{T}}.$$

PROVIDED SOLUTION:
Note that $|I_1(\nu,\varepsilon,X,T)|=$
    $$\left|\frac{1}{2\pi i}\int_{-\infty}^{-T}\left(-\frac{\zeta'}{\zeta}(\sigma+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma+it)\,X^{\sigma+it}\,dt\right|
      \ll\int_{-\infty}^{-T}\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|
      \cdot|\mathcal{M}(\tilde{1}_\varepsilon)(\sigma+it)|\cdot X^\sigma\,dt.$$
    Applying Theorem \ref{LogDerivZetaUniformLogSquaredBound} and Lemma \ref{MellinOfSmooth1b},
    we have that
    $$|I_1(\nu,\varepsilon,X,T)|
      \ll\int_{-\infty}^{-T}\log^2|t|\cdot\frac{X^\sigma}{\varepsilon\,|\sigma+it|^2}\,dt
      \ll\frac{X}{\varepsilon}\int_T^\infty\frac{\sqrt{t}\,dt}{t^2}
      \ll\frac{X}{\varepsilon\sqrt{T}}.$$
    Here we are using the fact that $\log^2 t$ grows slower than $\sqrt{t}$,
    $|\sigma+it|^2\geq t^2$, and $X^\sigma=X\cdot X^{1/\log X}=eX$.
-/
lemma I1NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) : ∃ (C : ℝ) (_Cnonneg : 0 ≤ C),
    ∀ {ε X T : ℝ} (_εinIoo : ε ∈ Ioo 0 1) (_Xgt3 : 3 < X) (_Tgt3 : 3 < T),
    ‖I1New SmoothingF ε X T‖ ≤ C * (X / (ε * Real.sqrt T)) := by
  admit

/-- **I5NewBound**

We have that
    $$|I_5(\nu,\varepsilon,X,T)|\ll\frac{X}{\varepsilon\sqrt{T}}.$$

PROVIDED SOLUTION:
By symmetry, note that
    $$|I_1(\nu,\varepsilon,X,T)|=|\overline{I_5(\nu,\varepsilon,X,T)}|=|I_5(\nu,\varepsilon,X,T)|.$$
    Applying Lemma \ref{I1NewBound} completes the proof.
-/
lemma I5NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ (C : ℝ) (_ : 0 ≤ C),
      ∀ {ε X T : ℝ} (_ : ε ∈ Ioo 0 1) (_ : 3 < X) (_ : 3 < T),
        ‖I5New SmoothingF ε X T‖ ≤ C * (X / (ε * Real.sqrt T)) := by
  admit

/-- **I2New**

Let
    $$I_2(\nu,\varepsilon,X,T)
      =\frac{1}{2\pi i}\int_{\sigma'}^\sigma\left(-\frac{\zeta'}{\zeta}(\sigma_0-iT)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma_0-iT)\,X^{\sigma_0-iT}\,d\sigma_0.$$
-/
noncomputable def I2New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ - T * I)))
/-- **I4New**

Let
    $$I_4(\nu,\varepsilon,X,T)
    =\frac{1}{2\pi i}\int_{\sigma'}^\sigma\left(-\frac{\zeta'}{\zeta}(\sigma_0+iT)\right)
    \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma_0+iT)\,X^{\sigma_0+iT}\,d\sigma_0.$$
-/
noncomputable def I4New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + T * I)))
/-- **I2NewBound**

We have that
    $$|I_2(\nu,\varepsilon,X,T)|\ll\frac{X}{\varepsilon\sqrt{T}}.$$

PROVIDED SOLUTION:
Note that $|I_2(\nu,\varepsilon,X,T)|=$
    $$\left|\frac{1}{2\pi i}\int_{\sigma'}^\sigma\left(-\frac{\zeta'}{\zeta}(\sigma_0-iT)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma_0-iT)\,X^{\sigma_0-iT}\,d\sigma_0\right|
      \ll\int_{\sigma'}^\sigma\left|\frac{\zeta'}{\zeta}(\sigma_0-iT)\right|
      \cdot|\mathcal{M}(\tilde{1}_\varepsilon)(\sigma_0-iT)|\cdot X^{\sigma_0}\,d\sigma_0.$$
    Applying Theorem \ref{LogDerivZetaUniformLogSquaredBound} and Lemma \ref{MellinOfSmooth1b},
    we have that
    $$|I_2(\nu,\varepsilon,X,T)|\ll\int_{\sigma'}^\sigma\log^2 T
      \cdot\frac{X^{\sigma_0}}{\varepsilon\,|\sigma_0-iT|^2}\,d\sigma_0
      \ll\frac{X\,\log^2T}{\varepsilon\,T^2}\int_{\sigma'}^\sigma d\,\sigma_0
      =\frac{X\,\log^2T}{\varepsilon\,T^2}\,(\sigma-\sigma').$$
    Here we are using the fact that $X^{\sigma_0}\leq X^\sigma=X\cdot X^{1/\log X}=eX$
    and $|\sigma_0-iT|^2\geq T^2$. Now note that
    $$|I_2(\nu,\varepsilon,X,T)|\ll\frac{X\,\log^2T}{\varepsilon\,T^2}\,(\sigma-\sigma')
      =\frac{X\,\log^2T}{\varepsilon\,T^2\,\log X}+\frac{FX\,\log T}{\varepsilon\,T^2}
      \ll\frac{X}{\varepsilon\sqrt{T}}.$$
    Here we are using the fact that $\log T\ll T^{3/2}$, $\log^2T\ll T^{3/2}$, and $X/\log X\ll X$.
-/
lemma I2NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) : ∃ (C : ℝ) (Cnonneg : 0 ≤ C),
    ∀ {ε X T : ℝ} (εinIoo : ε ∈ Ioo 0 1) (Xgt3 : 3 < X) (Tgt3 : 3 < T),
    let σ' := 1 - F / Real.log T
    ‖I2New SmoothingF ε X T σ'‖ ≤ C * (X / (ε * Real.sqrt T)) := by
    sorry

/-- **I4NewBound**

We have that
    $$|I_4(\nu,\varepsilon,X,T)|\ll\frac{X}{\varepsilon\sqrt{T}}.$$

PROVIDED SOLUTION:
By symmetry, note that
    $$|I_2(\nu,\varepsilon,X,T)|=|\overline{I_4(\nu,\varepsilon,X,T)}|=|I_4(\nu,\varepsilon,X,T)|.$$
    Applying Lemma \ref{I2NewBound} completes the proof.
-/
lemma I4NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ (C : ℝ) (_ : 0 ≤ C),
      ∀ {ε X T : ℝ} (_ : ε ∈ Ioo 0 1) (_ : 3 < X) (_ : 3 < T),
        let σ' := 1 - F / Real.log T
        ‖I4New SmoothingF ε X T σ'‖ ≤ C * (X / (ε * Real.sqrt T)) := by
  admit

/-- **I3New**

Let
    $$I_3(\nu,\varepsilon,X,T)
      =\frac{1}{2\pi i}\int_{-T}^T\left(-\frac{\zeta'}{\zeta}(\sigma'+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma'+it)\,X^{\sigma'+it}\,dt.$$
-/
noncomputable def I3New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ' + t * I)))
/-- **I3NewBound**

We have that
    $$|I_3(\nu,\varepsilon,X,T)|\ll\frac{X^{1-F/\log T}\sqrt{T}}{\varepsilon}.$$

PROVIDED SOLUTION:
Note that $|I_3(\nu,\varepsilon,X,T)|=$
    $$\left|\frac{1}{2\pi i}\int_{-T}^T\left(-\frac{\zeta'}{\zeta}(\sigma'+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma'+it)\,X^{\sigma'+it}\,dt\right|
      \ll\int_{-T}^T\left|\frac{\zeta'}{\zeta}(\sigma'+it)\right|
      \cdot|\mathcal{M}(\tilde{1}_\varepsilon)(\sigma'+it)|\cdot X^{\sigma'}\,dt.$$
    Applying Theorem \ref{LogDerivZetaLogSquaredBoundSmallt} and Lemma \ref{MellinOfSmooth1b},
    we have that
    $$|I_3(\nu,\varepsilon,X,T)|\ll\int_{-T}^T\log^2(2+T)
      \cdot\frac{X^{\sigma'}}{\varepsilon\,|\sigma'+it|^2}\,dt
      \ll\frac{X^{1-F/\log T}\,\sqrt{T}}{\varepsilon}\int_0^T\frac{dt}{|\sigma'+it|^2}.$$
    Here we are using the fact that this integrand is symmetric in $t$ about $0$
    and that $\log^2(2+T)\ll\sqrt{T}$ for sufficiently large $T$. Now note that,
    by Lemma \ref{DeltaRange}, we have
    $$\frac{1}{|\sigma'+it|^2}=\frac{1}{(1-\delta_T/3)^2+t^2}<\frac{1}{(41/42)^2+t^2}.$$
    Thus,
    $$|I_3(\nu,\varepsilon,X,T)|
      \ll\frac{X^{1-F/\log T}\sqrt{T}}{\varepsilon}\int_0^T\frac{dt}{|\sigma'+it|^2}
      \leq\frac{X^{1-F/\log T}\sqrt{T}}{\varepsilon}\int_0^\infty\frac{dt}{(41/42)^2+t^2}.$$
    The integral on the right hand side evaluates to $21\pi/41$, which is just a constant,
    so the desired result follows.
-/
lemma I3NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) : ∃ (C : ℝ) (Cnonneg : 0 ≤ C),
    ∀ {ε X T : ℝ} (εinIoo : ε ∈ Ioo 0 1) (Xgt3 : 3 < X) (Tgt3 : 3 < T),
    let σ' := 1 - F / Real.log T
    ‖I3New SmoothingF ε X T σ'‖ ≤ C * (X ^ (1 - F / Real.log T) * Real.sqrt T) / ε := by
    sorry

/-- **SmoothedChebyshevPull3**

We have that
    $$\psi_\varepsilon(X)=\mathcal{M}(\tilde{1}_\varepsilon)(1)\,X^1+I_1-I_2+I_3+I_4+I_5.$$

PROVIDED SOLUTION:
Pull contours and accumulate the pole of $\zeta'/\zeta$ at $s=1$.
-/
theorem SmoothedChebyshevPull3 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ' : ℝ}
    (σ'_pos : 0 < σ') (σ'_lt_one : σ' < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ' 2) ×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I1New SmoothingF ε X T -
      I2New SmoothingF ε T X σ' +
      I3New SmoothingF ε T X σ' +
      I4New SmoothingF ε T X σ' +
      I5New SmoothingF ε X T
      + 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by
  admit

/-!
\begin{theorem}[StrongPNT]
    We have
    $$\sum_{n\leq x}\Lambda(n)=x+O\left(x\exp(-c\sqrt{\log x})\right).$$
\end{theorem}
-/

/-!
\begin{proof}
\uses{SmoothedChebyshevClose, SmoothedChebyshevPull3, MellinOfSmooth1c, I1NewBound, I2NewBound,
  I3NewBound, I4NewBound, I5NewBound}
    By Theorem \ref{SmoothedChebyshevClose} and \ref{SmoothedChebyshevPull3} we have that
    $$\mathcal{M}(\tilde{1}_\varepsilon)(1)\,x^1+I_1-I_2+I_3+I_4+I_5
      =\psi(x)+O(\varepsilon x\log x).$$
    Applying Theorem \ref{MellinOfSmooth1c} and Lemmas \ref{I1NewBound}, \ref{I2NewBound},
    \ref{I3NewBound}, \ref{I4NewBound}, and \ref{I5NewBound} we have that
    $$\psi(x)=x+O(\varepsilon x)+O(\varepsilon x\log x)
      +O\left(\frac{x}{\varepsilon\sqrt{T}}\right)
      +O\left(\frac{x^{1-F/\log T}\sqrt{T}}{\varepsilon}\right).$$
    We absorb the $O(\varepsilon x)$ term into the $O(\varepsilon x\log x)$ term and
    balance the last two terms in $T$.
    $$\frac{x}{\varepsilon\sqrt{T}}
      =\frac{x^{1-F/\log T}\sqrt{T}}{\varepsilon}\implies T
      =\exp(\sqrt{F\log x}).$$
    Thus,
    $$\psi(x)=x+O(\varepsilon x\log x)
      +O\left(\frac{x}{\displaystyle\varepsilon\exp((1/2)\cdot\sqrt{F\log x})}\right).$$
    Now we balance the last two terms in $\varepsilon$.
    $$\varepsilon x\log x
      =\frac{x}{\displaystyle\varepsilon\exp((1/2)\cdot\sqrt{F\log x})}
      \implies\varepsilon\log x
      =\frac{\displaystyle\sqrt{\log x}}{\displaystyle\exp((1/4)\cdot\sqrt{F\log x})}.$$
    Thus,
    $$\psi(x)=x+O\left(x\exp(-(\sqrt{F}/4)\cdot\sqrt{\log x})\sqrt{\log x}\right).$$
    Absorbing the $\displaystyle\sqrt{\log x}$ into the
    $\displaystyle\exp(-(\sqrt{F}/4)\cdot\sqrt{\log x})$ completes the proof.
\end{proof}
-/

-- *** Prime Number Theorem *** The `ChebyshevPsi` function is asymptotic to `x`.
-- theorem PrimeNumberTheorem : ∃ (c : ℝ) (hc : c > 0),
--     (ChebyshevPsi - id) =O[atTop] (fun (x : ℝ) ↦ x * Real.exp (-c * Real.sqrt (Real.log x))) := by
--  sorry
