---
title: RiemannHIBS 当前状态
source: session
created: 2026-08-25
tags: [status]
schema_version: 2
audience: internal
last_confirmed: 2026-08-25
stage: current
---

# 当前状态 (2026-08-26)

> 完整实现图景见 [隐数坐标系中的黎曼猜想 — 完整实现](hidden-rh-implementation.md)：
> 翻译完备（机制环）+ 身份内禀（1/2 = 反射不动 + 能量平衡）+ 能量侧全内禀
> （对角调和/截断交叉/欧拉常数，无 Stirling）+ 一一对应闭环；剩余缺口 R1（交叉
> o(T) 形式化）与 R2（平衡点→共圆 = RH 本身）。

## 已证 (无 sorry)
| 定理 | 位置 | 内容 |
|------|------|------|
| criticalLine_circle | Analytic.lean §6 | ‖exp(1/2+it)‖ = √e: 临界线像 = 圆周 |
| eta_eq_mul_zeta | Analytic.lean §4 | η = (1−2^{1−s})·ζ (Re s>1) |
| criticalPhaseC_envelope_circle | §7 | 相位截面经指数映射共圆 √e |
| expZeta_phase_principal | §8 | ζ̂(r·e^{iθ}) = ζ(log r + iθ) 主支 |
| phase_periodic / fold | §8 | 多圈叶 2πk 周期; 叶 π+2πk 折叠到负实轴 |
| envelope_universal_cover_branch | §8 | 每圈 k 有主支相位原像 |
| log_sqrt_exp_one | §11 | log(√e) = 1/2 (半径基本单位, 长度→对数) |
| critical_leaf_norm_locked | §11 | 临界叶上每项模长锁定 n^{-1/2} (长度维度锁定) |
| term_winding_number | §11 | 第 n 项缠绕圈数 = log(n+1) (windingCount, 角速度×叶数) |
| absolute_convergence_outside_critical_leaf | §11 | 绝对收敛分界 r>e (圆外更远叶绝对收敛) |
| critical_leaf_not_absolutely_convergent | §11 | 临界叶 (r=√e<e) 不绝对收敛 |
| zetaCoverIsomorphism | §12 | 覆盖↔复平面同构结构: covers(覆盖双射)+radial(径向单射)+zeta_eq(ζ 值一致)+branch(螺旋延续)+periodic(多叶折叠) — 全部由已证定理构成, 无 sorry |
| helix_continuation | §12 | 螺旋线延续: 每个 w≠0 的每圈 k 都有主支相位原像 (把"螺旋无限延伸"与"可数多叶"接起来) |
| mechanism_cycle_closed | §13 | 机制完备环 A⟹B⟹C⟹D⟹A 四方向全证 (A 圆外无零点⟹B 零点在圆上⟹C 包络半径锁定‖e^s‖=√e⟹D 经典 RH⟹A), 输入 h0: 0<Re s |
| zero_free_outside_envelope | §14 | 圆外远处无零点: Re(s)≥1 ⟹ ζ(s)≠0 (欧拉乘积每因子非零, mathlib riemannZeta_ne_zero_of_one_le_re) |
| zero_free_negative_side | §14 | 负侧无非平凡零点: Re(s)≤0 ⟹ ζ(s)≠0 (函数方程反射 + 14.1, 非负整数外) |
| nontrivial_zero_in_critical_strip | §14 | 非平凡零点 ⟹ 0<Re(s)<1 (临界带): 由 14.1+14.2 排除两侧 |
| nontrivial_zero_in_envelope_annulus | §14 | 非平凡零点 ⟹ 1<‖e^s‖<e (圆环内): ‖e^s‖=e^{Re s}, 临界叶√e 是圆环几何平均正中 |
| inversion_preserves_annulus | §14.5 | 反演 w↦e/w 保持圆环 1<‖w‖<e |
| AnnularNontrivialZero / annularNontrivialZero_of_zero | §14.5 | 将非平凡零点封装为“临界带 + 隐数圆环”对象 |
| reflection_involutive | §14.5 | s↦1−s 是 involution |
| annularNontrivialZero_reflects / _iff_reflects | §14.5 | 圆环内非平凡零点集合在反射下闭合且可逆；平凡负偶零点因前提排除不被误反射 |
| on_circle_reflects_on_circle | §14.5 | 临界叶/圆周由反演保持；这是集合保持，不是圆上每一点的点点固定 |
| exists_annular_nontrivial_zero_pair | §14.5 | 若已有一个圆环内非平凡零点，则可构造其反射对；不推出无限性 |
| hiddenStripWindow | §14.5 | 覆盖空间中的有限高度提升矩形：0<Re(s)<1 且 |Im(s)|<T，保留螺旋角度而不折叠 |
| hiddenNontrivialZeroHeights / HiddenZeroHeightGrowth | §14.5 | 将圆环非平凡零点映到覆盖高度 |Im(s)|；定义高度无界的精确分析接口 |
| infinite_annular_nontrivial_zeros_of_height_growth | §14.5 | 高度集合无界 ⟹ 圆环内非平凡零点集合无限（纯集合论桥） |
| infinite_nontrivial_zeros_of_hidden_height_growth | §14.5 | 同一高度增长接口 ⟹ 经典临界带中的非平凡零点集合无限 |
| hiddenLiftRectangle | §14.5 | 覆盖空间中的对称有限高度矩形，保留 θ=Im(s) 叶坐标 |
| hiddenRectangleBoundaryIntegral | §14.5 | 将提升矩形四条边写成隐数坐标的边界积分 |
| hiddenRectangleBoundaryIntegral_eq_zero_of_differentiableOn | §14.5 | 全纯函数在提升矩形边界上的积分为零（调用 mathlib Cauchy–Goursat 矩形原子） |
| analyticAt_riemannZeta | §21 | 对每个 s≠1，利用去心邻域可微与连续性证明 ζ 在 s 处解析 |
| logDeriv_circle_integral_eq_zero_of_zero_free | §21 | 圆盘无极点且无零点时，ζ 的对数导数圆周积分为零 |
| exists_closedBall_zero_of_logDeriv_integral_ne_zero | §21 | 对数导数圆周积分非零 ⟹ 闭圆盘内存在 ζ 零点（无零点结论的逆否） |
| AnnulusZeroWitness / CriticalStripWitness | §21 | 将“有限圆盘 + 非零绕数”及其临界带约束封装为可验证的存在性见证 |
| ZeroHeightSupply | §22 | 显式的经典分析输入：任意高度 H 之上存在临界带零点；不是 axiom，也尚未被证明 |
| hiddenZeroHeightGrowth_of_zeroHeightSupply | §22 | 高度供给 ⟹ 隐数覆盖中的零点高度无界 |
| infinite_nontrivial_zeros_of_zeroHeightSupply | §22 | 高度供给 ⟹ 无限多个非平凡零点；完整证明仍依赖未实现的高度供给输入 |
| logDeriv_integral_eq_zero_of_analytic_ne_zero | §23 | 一般函数版 Cauchy: 闭盘上解析且非零的 g, 其 log 导数围道积分为零 |
| powFactor_logDeriv_eq / winding_of_pow_factorization | §23 | 幂因子分解核心原子: f=(z−w)^m·g ⟹ ∮f'/f = 2πi·m (logDeriv_mul/pow/comp 组合路线, 规避 nat 减法幂代数) |
| ZetaSimpleZeroCertificate (U,w,g 参数化) | §24 | ζ 单零点局部证书: 开集 U 上 ζ(z)=(z−w)g(z), g 全纯非零; 零点 w 与因子 g 为显式参数使全部字段为命题 |
| certificate_gives_zero | §24 | 证书直接推论: ζ(w)=0 (factorEq 在 w 处取值) |
| zeta_winding_eq_two_pi_i_of_certificate | §24 | 证书 ⟹ ∮ζ'/ζ = 2πi (U 开保证 deriv 局部相容 + 23.3 套用) |
| annulusZeroWitness_of_zetaCertificate / exists_annular_pair_of_zetaCertificate | §24 | 证书 ⟹ AnnulusZeroWitness (接§21) ⟹ 圆环零点反射对 (接§21.5), 全下游自动接通 |
| UnboundedZetaCertificateAssumption | §25 | 无界证书族 (外部分析输入声明, def 形态非 axiom): 任意高度之上都有临界带内单零点证书实例 |
| zeroHeightSupply_of_certificateFamily | §25 | 第二步主桥: 证书族 ⟹ ZeroHeightSupply (certificate_gives_zero + 盘在临界带内) |
| classicalZeroCountGrowth_of_zeroHeightSupply | §25 | 第三步补桥: 高度供给 ⟹ 经典计数增长 (无限集取 N+1 有限子集, 高度像最大值定窗, encard 单调) |
| no_zero_of_boundary_dominance | §26 | 零点隔离工具 I (排除半边): g 解析无零点 + ‖h/g‖≤q<1 于圆周 ⟹ g+h 开盘内无零点 (最大模原理路线) |
| zeta_ne_zero_of_boundary_unit_bound | §26 | ζ 排除判据: 圆周上 |ζ−1| 一致 <1 且盘避开 s=1 ⟹ 盘内 ζ≠0 (数值路线边界安全验证形态) |
| xiEntire / differentiable_xiEntire / xiEntire_one_sub | §27 | ξ 整函数载体 (Hadamard 路线): 经 Λ₀ 代数形态 ξ(s)=(1/2)s(s−1)Λ₀(s)+1/2 — 整性与对称性成为纯多项式推论, 无需 removable singularity 分析 |
| xiEntire_eq_mul_zeta / xiEntire_eq_zero_iff_zeta_zero | §27 | 临界带内 ξ(s)=(1/2)s(s−1)Γℝ(s)ζ(s) 显式公式 + 零点桥 ξ=0 ⟺ ζ=0 (Γℝ≠0 由 Gamma_ne_zero_of_re_pos) |
| critical_leaf_diagonal_energy_term / critical_leaf_diagonal_energy_diverges | §11+ (Hardy) | 能量种子发散已证: 对角能量单项 ‖a_n‖²=(n+1)^{-1} 纯代数; 调和级数 ¬Summable — Hardy 1914 绕开 Stirling 的丰度来源 |
| Real.gamma_ge_pow_mul_self | §29 | Γ 递推下界 (Hadamard 链 [G] 环节): Γ(x+n) ≥ xⁿ·Γ(x) 对 x≥1, 经 Real.Gamma_add_one 归纳迭代 — 完全初等, 无需 Stirling |
| rotVecOnLine / dirichletPartialSumLine | §31 | 缺口 A 技术模板: 临界线旋转向量与有限 Dirichlet 部分和的显式定义 |
| integral_rotating_atom | §31 | 旋转积分原子: ∫exp(iΔx)dx = (e^{iΔT}−e^{−iΔT})/(iΔ), Δ≠0 (自证 HasDerivAt 原函数; mathlib 同名引理因 module 系统迁移暂不可见) |
| energy_single_term_integral | §31 | 对角能量积分: ∫‖v_n‖² = 2T·(n+1)^{-2σ} — "log 积累"进入计算的精确位置; N→∞ 后对角和 Σn^{-2σ} 在 σ=1/2 发散为 Σn^{-1} |
| infinitely_many_trivial_zeros | §15 | 零点集合为无限集: 单射嵌入 n↦−2(n+1), 每个是平凡零点 ζ(−2(n+1))=0 |
| argumentPrinciple_single_zero | §16 | 隐数坐标系幅角原理原子: ∮dz/(z−w)=2πi (w 在圆内, mathlib circleIntegral) |
| envelope_circle_param | §16 | 圆 |z−c|=r 在相位包络坐标 = θ↦c+r·e^{iθ} (hEvalPhase 即圆参数化) |
| phase_winding_equals_zero_count | §16 | 相位缠绕 = 零点数×2πi (logDeriv 表述: 绕零点一圈相位变化 2π) |
| zeroCount_normalized | §16 | (2πi)⁻¹·∮dz/(z−w)=1 (幅角原理归一化: 除以 2πi 得零点数) |
| zeta_growth_decomposition | §17 | ζ(s) = completedRiemannZeta(s) / Γℝ(s) (mathlib 已证, 坐标无关增长分解) |
| gammaR_norm_decomposition | §17 | \|Γℝ(s)\| = π^(−Re s/2)·\|Γ(s/2)\| (Gammaℝ 模长坐标读法, 纯代数) |
| gammaR_norm_in_envelope_coords | §17 | 临界叶 \|w\|=√e 上 \|Γℝ\| = π^(−1/4)·\|Γ((log√e+iθ)/2)\| (隐数坐标精确表达式) |
| zeta_norm_in_envelope_coords | §17 | 覆盖坐标 \|ζ(log r+iθ)\| = \|compZ\| / (π^(−log r/2)·\|Γ((log r+iθ)/2)\|) (增长起点) |
| phaseCancelRelation | §18 | 有限相位抵消: 有限整数组合 Σaᵢ·log(nᵢ) ∈ 2πℤ (360° 圆周回原点) |
| phaseCancel_of_exp_one | §18 | 相位抵消 ⟹ exp(i·Σaᵢ·log(nᵢ)) = 1 (复指数/单位圆乘积取 1, 用 Complex.exp_eq_one_iff) |
| phaseCancel_zero_iff_powProduct_one | §18 | 抵消回 0 度 ⟺ Π(nᵢ+1)^{aᵢ} = 1 (精确有限相位抵消 ⟺ 整数乘法结构, 不依赖超越性) |
| phaseShift_cancel_of_int | §18.6 | 一个组合×整数角度: 平移后窗口相位 = -t·phaseCancelSum, 整数 t 下为 2π·整数 (旋转向量相位线性性, 无 sorry) |
| phaseShift_aligned_at_integer | §18.6 | 对齐窗口在整数平移下保持对齐 (相位仍 2πℤ); = "一种组合×整数步反复对齐"的代数真身; 不单独推出 ζ 零点 (尾项/增长另需) |
| ModulatedZetaFamily | §18.8 | 调制基元族 = 无界证书族 (命名封装: 每个高度 H 配一个单零点证书 = "同一类基元随 H 无限调制") |
| zeroHeightSupply_of_modulatedFamily | §18.8 | 调制基元族 ⟹ ZeroHeightSupply (复用证书族主桥 zeroHeightSupply_of_certificateFamily) |
| infinite_nontrivial_zeros_of_modulatedFamily | §18.8 | 调制基元族 ⟹ 无限非平凡零点 (复用既有全链); 诚实: 族的具体实例(每高一个证书) 仍是分析供给黑盒, 未提供 |
| eta_term_rotating_vector | §19 | η 第 n 项 = (−1)^n × 旋转向量 (复恒等式, `dirichlet_term_rotating_vector` 反向 rw + ring) |
| eta_phase_alignment_condition | §19 | 缺口①桥 (Re>1): η(s)=0 ⟺ 交错旋转向量和=0 (镜像 §10, 换 η 交替符号) |
| alignmentZero | §20 | 隐数对齐零点: s 的对齐零点 ⟺ 其交错旋转向量 (η 形态) 和为零 (零点=相位对齐的信息压缩表述) |
| alignmentZero_iff_zeta_zero | §20 | Re>1 桥 (前提排斥因子≠0): alignmentZero s ⟺ riemannZeta s = 0 (经 eta_eq_mul_zeta); 隐数对齐投到经典零点 |

## 声明 (非证明)
- RiemannHypothesisHidden / C / Phase: RH 的隐数翻译
- riemannHypothesis_hidden_of_mathlib: 经典 RH ⟹ 隐数版 (单向)
- EnvelopeUniversalCoverMultiLog: 多值 log 分支 (draft)
- 非平凡零点无限多 (Hadamard 1893): 已证仅覆盖平凡零点 (§15); 非平凡部分需增长阶 + 因子分解/幅角原理; 已有机理皆"必要条件/缺增长"型, 不携带 ζ 的增长行为, 如实标注边界

## 诚实边界 (核心!)
- 圆外远处无零点已证 (Re≥1, §14 欧拉乘积); 但 1/2<Re<1 的圆外部分 (=RH 核心未解区) 仍未被覆盖 — 机制链"圆外无零点"现在分两段: 远处已证, 临界带内仍是 RH
- 机制完备环 (§13) 是"四方式等价"而非"零点真在圆上"的证明: 输入 h0 (`0 < Re s`, 零点在右半平面) 为显式机制假设 (经典事实但尚未在形式化层实现); D = `RiemannHypothesis` (mathlib 声明) 仍为被设对象 — 环的含义是"**若 RH 成立则四种说法一致**", 环本身不给 RH 真值。A⟹B 已证 (§9), 但 D⟹A 借 RH 声明, 闭环仍赖 RH 真值。
- 幅角原理 (§16) 已构造为隐数坐标系内的机制原子 (相位缠绕=零点数), 但它是"电路"缺"电源": 无限零点的输出依赖 ζ 在围道边界的增长估计 (N(T)~T/2π·log(T/2π)) — 该输入是 ζ 的分析性质, 坐标变换翻译不掉, 非平凡零点无限多仍标注为边界
- §17 增长分解: ζ(s)=compZ/Γℝ 的精确坐标读法已证 (gammaR_norm_decomposition / zeta_norm_in_envelope_coords, 纯代数), 但预言 P1–P3 (Stirling 渐近 + 完成ζ 有界性) mathlib 均未形式化 — "无限非平凡零点"唯一缺失的分析输入已被显式隔离为待形式化边界 (draft), 不代表证明取得进展
- §18 有限相位抵消: 精确组合翻译已证 (有限整数组合抵消 ⟺ 整数幂关系, 纯代数/整数结构, 不依赖超越性); 但它只回答"哪些有限组合能抵消", 不回答"抵消 ⟹ 全部零点在临界线" (RH 核心仍缺); 路线 B 稠密性 (log 的 ℚ-无关) 依赖超越性, mathlib 未形式化, 如实标注阻塞
- **无限非平凡零点 = 目标命题 G (2026-08-25 精确化)**: `Set.Infinite {s | riemannZeta s = 0 ∧ 非平凡 ∧ s ≠ 1}`. 关键概念区分(不能混淆): (i) 平凡零点无限(§15)靠**显式公式** ζ(−2(n+1))=0, 无需分析; (ii) 非平凡零点无限缺**存在性** — `alignmentZero`(§20) 是**谓词**(判定某 s 是否对齐), 不保证任何 s 存在, 更不保证无限多个互异 s. (iii) "逐项模长锁定 n^{−1/2}"(§11)≠"完成ζ整体有界"(§17 P2) — 后者(未证)才是幅角/零点计数输入. 所需组件: ①存在性(围道边界变号/幅角绕数非零, 需 differentiableAt+边界估计) ②无限性 N(T)→∞(完成ζ有界 P2 + 幅角计数, 均未形式化) ③翻回隐数螺旋坐标(θ→∞↔t→∞). 螺旋增长模式可先定义为对象(spiralGrowth 剖面), 把"统一证明"收敛为可攻坚缺口, 但**增长界本身未证, 不装证无限**
- **"圆上无限点⟹存在性已建立" 判定 (2026-08-25)**: **不成立** — 几何连续的无限被错当成了函数零点的无限. 圆(圆周)是连续几何, 有不可数多个点, 这是公理性质; 但 ζ 的非平凡零点是**离散取 0 的点** — "圆上有无限个点" ≠ "ζ 在圆上有无限个零点". 前者是集合无限, 后者是函数取零位置的存在性; 从"圆连续"不能推出"有零点", 更不能推出"无限个". §22 已将唯一黑盒压缩为 `ZeroHeightSupply`(任意高度之上存在临界带零点), 而"圆连续无限"不提供**任何一个**具体零点实例, 故不能补该输入. "圆外无零点 + 圆环定位"同样只排除/定位, 不足以证明"存在零点且恰在圆上".
- **隐数驱动的存在性构造 (候选路线, 非已证)**: 可在万有覆盖取有限高度的螺旋矩形/圆环扇区 `Ω_T`, 对提升函数 `ζ̂(s)=ζ(s)` 或完成函数建立“边界无零点 + 边界像绕数非零”的见证，再由幅角原理推出 `Ω_T` 内至少一个零点，并经 `w=e^s` 翻回包络圆环。要得到无限多个需构造无界序列 `T_j` 或证明 `N(T)→∞`. `critical_leaf_norm_locked`、`phaseCancelRelation`、`periodicCancelWindow` 单独不足以完成这一步：有限项抵消不等于带尾项控制的 ζ 零点，而且不同覆盖叶上的 ζ 值一般不周期重复。隐数坐标的真实贡献是把围道、反演、相位与叶结构组织成可验证的存在性见证，不是凭坐标变换凭空产生零点。
- **§14.5 高度接口已落地但输入未证**: `hiddenStripWindow` 保留覆盖角度 `θ=Im(s)`；`HiddenZeroHeightGrowth` 精确定义“圆环非平凡零点高度无界”，并已证明它推出无限非平凡零点。尚未证明 `HiddenZeroHeightGrowth` 本身；下一分析输入应是完成 ζ 在有限高度提升矩形边界上的非零绕数/零点计数增长。
- **「e→1/2」已证的是「圆的身份」而非「零点在圆上」(2026-08-26 纠偏)**: `envelope_inversion_fixed_circle`+`log_sqrt_exp_one` 已证「反演不动圆 = √e, 取 log = 1/2」——这解释了临界线**为何是 1/2 这个位置身份**(坐标系独有, 经典无从提出). 但 `envelope_inversion_eq_conj_on_circle` (`e/w=conj w`) 是全圆几何恒等式, 只给出条件句「若零点在圆上则成自共轭对」, **不推出零点在圆上、更不推出存在零点**. 「零点在圆上」= §13 机制环 B 的 `hno` 输入, 非 e 单独给出. 故「e 解释位置」须严格限定为层①(圆的身份), 不可越界到层②(零点在圆上)或丰度(无限). 同类第三只已否跳跃: e 的自共轭圆 ≠ ζ 无限零点来源(见「坐标系独有规律」小节).
- **围道/存在性桥已分层落地**: `hiddenLiftRectangle` 与 `hiddenRectangleBoundaryIntegral` 已接入矩形 Cauchy–Goursat；§21 另已证明圆盘内 ζ 无零点时 `logDeriv` 圆周积分为零，并给出其逆否存在性桥。尚未完成的是一般矩形 `logDeriv` 零点计数、边界绕数见证，以及完成 ζ 的增长输入。
- **缺口① (推导结论)**: `zeta_phase_alignment_condition` (§10) 用 `zeta_eq_tsum` 把 Re>1 的零点转成旋转向量和=0; 其旋转向量核 `dirichlet_term_rotating_vector` 是**复数恒等式且与 σ 无关** (可对任意 σ 用). 临界带 0<Re<1 的断路点在"级数换谐"(ζ 的 Dirichlet 展开) 而非相位机制. **正解 (已推明)**: 在临界带 `ζ(s)=0` 是良定义全纯函数取零 (`differentiableAt_riemannZeta`, s≠1), 不需级数和; "相位对齐判定" 的隐数语义 = 覆盖空间里 `expZeta_phase_principal` 把 `ζ̂(w)=ζ(log r+iθ)` — "对齐零点" 在隐数即此良定等式. 跨到经典: Re>0 用 η(交替)是 Abel 条件收敛, 排斥因子 `(1−2^{1−s})` 在临界带**恒非零** (2^{1−s}=1 只在 s=1+2πik/ln2, 实部=1, 不在 0<Re<1), 故 ζ=0⟺η=0 在临界带成立 (经典)。**真正缺口 = 条件收敛(η)+Abel/函数方程延拓 的 mathlib 工具缺失**, 非概念不可能; 落地建议 = 覆盖语义做"对齐零点"命题 + 临界带诚实标注未形式化. **状态 (2026-08-25)**: §19 已在 Re>1 落地可编译的 η 交错桥 (eta_term_rotating_vector + eta_phase_alignment_condition, 无 sorry); 临界带 0<Re<1 仍缺条件收敛 η + Abel/函数方程正则化工具, 如实标注为待形式化
- **缺口② (增长→无限零点)**: 幅角原理 (§16) + 增长分解 (§17) 已把 "N(T)→∞" 隔离为唯一缺失分析输入 — 依赖 Stirling 渐近 + 完成 ζ 有界性 (P1–P3), 二者 mathlib 均未形式化; 即使完成也只证"无限多", 不等于 RH (临界带上) — 如实标注
- **§21 存在性桥已完成但没有伪造见证**: `analyticAt_riemannZeta`、无零点时的 `logDeriv` 圆周积分为零，以及其逆否命题均已无 `sorry` 编译；`AnnulusZeroWitness` / `CriticalStripWitness` 把“积分非零”精确封装为唯一输入，但代码没有声称存在这样的见证
- **§22 分阶段闭环已完成**: `ZeroHeightSupply` 是 `N(T)→∞` 的直接弱化接口；它可推出 `HiddenZeroHeightGrowth`，再推出无限非平凡零点。当前仍未完成的是从 completed ζ、Stirling 与完整幅角/零点计数证明 `ZeroHeightSupply`，因此项目尚未拥有无条件的无限非平凡零点证明
- **阶段① 局部存在性的 Hardy 数值路线阻塞 (2026-08-25)**: 三阶段路线中"有限高度零点证书"(Z(a)Z(b)<0 + IVT ⟹ Z(t)=0 ⟹ ζ(1/2+it)=0) 需要严格区间算术验证数值不等式 — mathlib 当前无 interval arithmetic 基建, 浮点计算不可作 Lean 证明. 已落地替代接口: `ZetaSimpleZeroCertificate` 把数值路线终点表达为纯代数谓词, 任何供给路线 (Hardy 数值/Stirling 组装/Hadamard 无限性反推) 到手后全下游自动接通
- **幅角原理完成度**: §23 已落地单零点幂因子绕数原子 (∮f'/f = 2πi·m); 完整幅角原理 = 该原子 + 有限零点集枚举 (多零点求和), Riemann–von Mangoldt 还需 Stirling 增长估计 — 后两者仍未形式化
- **§25 语义澄清 (2026-08-25)**: `UnboundedZetaCertificateAssumption` 是外部分析输入的条件谓词 (def 形态, 非 axiom 非已证) — §25 真正证明的是"若任意高处都能提供严格单零点证书, 则非平凡零点无限多", 尚未证明"任意高处的证书存在"; 后者仍需 Hardy / Riemann–von Mangoldt / 严格数值隔离. 当前全链: CertificateFamily ⟹ Supply ⟹ HeightGrowth ⟹ 无限; CertificateFamily ⟹ Supply ⟹ CountGrowth ⟹ HiddenCountGrowth ⟹ 无限
- **§31 缺口 A 地基状态 (2026-08-26)**: 有限 Dirichlet 多项式的 L² 均值展开已落地前两块 (旋转积分原子 + 对角能量积分); 双重和展开主定理 (ΣΣ w_m w_n ∫exp 形态) 与取极限步骤 (Abel/一致收敛控制) 未形式化. 技术发现: mathlib 正在迁移 module 系统, Analysis/SpecialFunctions/Integrals/Basic 的部分定理暂非 public, 相关引理需自证
- **Hadamard 组合链依赖图状态 (§28/§29, 2026-08-26)**: [A]条带内ζ上界(η/Abel量化)未形式化 → [B]Γ粗上界(积分拆分)未形式化 → [C]ξ上界组合依赖AB → [D]Borel–Carathéodory **✅mathlib已有** (Complex.borelCaratheodory) → [E]BC应用+Cauchy估计→G常数→h=e^{bs} 未形式化 → [F]对称性强迫多项式 (轻,代数,xiEntire_one_sub已备) → [G]**✅Γ递推下界已证** (Real.gamma_ge_pow_mul_self) → [H]实轴矛盾组装(轻). 两端已有基建, 中段[A][B][E]是剩余工作量; B-C链补的是Hadamard侧反证组合(Hadamard版缺口B), 不补Hardy均值公式缺口(A)
- **Hadamard 路线初等化发现 (2026-08-26, §27)**: 非平凡零点无限多的整函数载体 ξ 已落地 — 关键是 mathlib 的 completedRiemannZeta₀ (去极点辅助整函数) 经代数变形 ξ=(1/2)s(s−1)Λ₀+1/2 使整性/对称性免费. **Stirling 并非丰度必经之路**: 增长上界只需 Euler 积分拆分粗界 |Γ(s)|≤e^{O(|s|log|s|)}, 实轴下界只需 Γ 递推 Γ(x+n)≥xⁿΓ(x) — 全初等. 组合链 (Borel–Carathéodory → logDeriv 常数 → 对称强制多项式 → 实轴矛盾) 未形式化, mathlib BorelCaratheodory.lean 已侦察存在
- **零点隔离完成度 (§26)**: 排除半边已落地 (`no_zero_of_boundary_dominance` 最大模原理路线); 存在半边 (主导线性项 ⟹ 恰一个零点) 需要 winding number 整数性/同伦不变性 — mathlib 缺失该理论 (已侦察确认), 完整 Rouché 待基建
- 螺旋无限延伸 ≠ 全称证明: 舞台(覆盖)完备 ≠ 演员(零点)在台上
- 非平凡零点存在性与无限性: 已证仅平凡零点无限 (§15); 非平凡部分需增长阶+因子分解/幅角原理, 已有机理皆"必要条件/缺增长"型, 不携带 ζ 的增长行为, 如实标注边界

## e 的独有规律：位置与丰度分离

在隐数坐标 `w=e^s` 下，`e` 在临界结构中的三个出现位置来自同一个反射/反演不动机制：

1. 函数方程反射 `s↦1−s` 变成包络反演 `w↦e/w`；其不动圆满足 `|w|²=e`，所以半径是 `√e`。
2. `|w|=e` 等价于 `Re(s)=1`，是圆环 `1<|w|<e` 的外边界，也是 Dirichlet 绝对收敛分界在隐数坐标中的表达。
3. `log(√e)=1/2`，因此不动圆的半径在对数坐标中正好选出临界线 `Re(s)=1/2`。

这给出坐标系独有的真实解释：`e→√e→1/2` 说明为什么反射自共轭结构选中临界位置。它不说明零点一定落在该圆上，也不说明圆上存在无限多个零点。前者需要排除临界带内偏离圆的零点，后者需要零点存在/增长输入；因此 **e 规律解释位置，不自动解释丰度**。

### 三个精确化 (2026-08-26 补)

4. **圆上反演 = 共轭 (已证)**: `envelope_inversion_eq_conj_on_circle` (Analytic.lean §6 机制 e) — `‖w‖=√e ⟹ e/w = conj w`. 反射作用在不动圆上**恰好就是复共轭**: 这是全部半径中唯一发生"镜像=自共轭"的圆. 零点若在此圆上, 其函数方程反射对即共轭对 — "临界线上零点天然自配对"的几何表达.

5. **不动圆唯一性 (取正根的必然性)**: 不动条件 `|e/w|=|w|` 给 `|w|²=e`, 正实数解**唯一**为 `√e`. 因此"自共轭圆"只有一条, 它对数化后必是 `Re(s)=1/2` — 不是众多候选之一, 而是反射几何的唯一解. 这把"为什么 1/2"从约定升级为结构必然 (前提: 零点在某个反射不变集上).

6. **丰度瓶颈的精确表述**: 自共轭圆是**连续**一维对象; 其上的离散子集(零点集)基数可为有限也可为无限 — 连续性不向离散子集传递任何基数信息. 故"这条线唯一且特殊"(位置, e 几何已解释) 与 "这条线上有无限个离散点"(丰度, 需绕数/增长/存在性供给即 §16/§22 接口) 是**正交问题**. e 几何对丰度的贡献为零; 任何"从自共轭性推出无限多"的推理路线都缺少中间环节.

## 坐标系独有规律 (e 的几何身份)

这是隐数坐标系 `w=e^s` **独有、经典复平面根本没有**的一条可精确化规律。经典里临界线只是「Re s=1/2」这条凭空画的线；隐数里这条线的身份是**被 e 唯一选定的**。

**已证内核 (不带任何未证输入):**
- 函数方程反射 `s↦1−s` 在包络坐标 = 反演 `w↦e/w` (`envelope_inversion_map`, §13).
- 反演的不动集恰为圆周 `‖w‖=√e` (`envelope_inversion_fixed_circle`, §13): `‖e/w‖=‖w‖ ⟺ ‖w‖²=e ⟺ ‖w‖=√e`.
- 取对数即得 `log(√e)=1/2` (`log_sqrt_exp_one`, §11). **所以「1/2」不是常数定义，是反演不动圆半径的必然对数值.**
- 不动圆上反演 = 共轭: `e/w = conj w` 对**任意** `‖w‖=√e` 的点成立 (`envelope_inversion_eq_conj_on_circle`, §13) — 这是全圆几何恒等式, 非零点专属.

**「位置」必须拆成两层 (关键辨析, 2026-08-26):**
- 层① **圆的身份** (已证): 若反射对称要有一个「固定尺度」的圆, 它**必是** `√e`, 对应 `1/2`. e 唯一选中了 1/2 这个位置身份. 这一层是坐标系独有、且已证.
- 层② **零点在圆上** (未证输入): 由层① + 反演=共轭, 只能推出*条件句*「若有个零点 w 在圆上, 则其反射 partner `e/w` = `conj w` (自共轭对)」. 它**不推出任何点在圆上, 也不推出有零点**. 零点确实在圆上 = §13 机制环 B, 依赖 `hno` (圆外无零点) 这个显式机制假设, 非 e 单独给出.
- 因此「e 解释位置」的准确含义是**仅层①**: e 解释「临界线为何是 1/2 这个身份」, 不解释「零点为何/是否在那条线上」(层②).

**丰度 (为何无限) — e 完全不涉及 (诚实边界):**
- e 给出的是**一个半径 / 一条一维圆 (线)**. 线是连续几何, 有不可数个点——这是公理, 不是 ζ 给的.
- ζ 非平凡零点是**离散取零位置**. 从「圆是 √e 这条线」推不出「线上有哪怕一个 ζ 零点」, 更推不出「无限个」.
- 仓库唯一诚实的「无限」接口仍是 `HiddenZeroHeightGrowth` / `ZeroHeightSupply` (§14.5/§22) — 那是 ζ 的增长/存在性分析输入, 非 e 的几何能生成.
- 同类已否跳跃 (务必区分): ①「圆上无限点⟹存在性」(2026-08-25 已否 — 几何连续无限 ≠ 函数零点无限); ②「有限相位组合⟹无界高度」(2026-08-25 已否 — 退化判定 phaseCancelSum=0); ③本次「e 的自共轭圆⟹无限零点」属同类第三只: 把坐标变换几何误当 ζ 零点存在来源.

**作为开放真问题 (推进价值):** 「为什么偏偏是这个 e?」的答案是 e 来自函数方程 `e^{1−s}=e/e^s` 里的那个 `e`, 而它的平方根半径正是反射对称能「固定」的唯一尺度. 这把「临界点为什么是 1/2」从经典的定义提升为坐标系内的几何必然 — 是经典框架根本无从提出的深刻问题. 它的边界已厘清: 这是关于「位置身份」的真洞察, 不是「存在/无限」的来源.

## 已验证: 隐数坐标的「相位预算」是真实可操作的量 (§11.5, 2026-08-26, Lean 编译通过)

应「丰度能否在隐数坐标做」之问, 实际在 Lean 中形式化验证了「临界圆上的相位预算」——不是文档猜想, 是 `lake build` 通过的真定理:

- `critical_leaf_phase_velocity_term_norm` (§11.5): 第 n 项相位速度 ‖S'(θ) 单项‖ = (n+1)^{−1/2}·log(n+1), 纯代数 (`ring`/`norm_mul` 级, 不依赖收敛性).
- `critical_leaf_phase_velocity_budget_increasing` (§11.5): 预算随 N 单调累积, 第 N+1 项新增正贡献.
- `critical_leaf_phase_velocity_positive` (§11.5): 对 N≥1 该贡献恒 >0 — 验证「隐数坐标能承载丰度指标」这一元问题在**代数/语法层非死路**.

**含义**: 隐数坐标里「零点诞生 = 多角速度旋转向量相位对齐相消」(§11 机制 b) 的相位结构, 其「预算」是 Lean 可直接操作的真实量; 方向 A (临界叶相位预算) 从语法层确认可行, **不**是已被否的「有限相位组合⟹无界」那种退化.

**诚实边界 (最关键)**: 这三条只证「预算在累积」, **不证**「预算在某 θ 被迫归零 ⟹ 零点」. 后者需要尾项 Σ_{n≥N}(n+1)^{−1/2}·e^{−iθ·log(n+1)} 受控, 即临界圆上**条件收敛级数的尾项估计** — 正是 §17 P1–P3 的 Stirling 输入缺口. 数值上 Σ_{n≥N} n^{−1/2}·... 的尾项 ~ N^{1/2}·(振荡), **不趋于 0**, 所以「预算累积⟹归零」在临界圆上**不成立** (除非借 Stirling 增长把整体 |ζ| 压下来, 回到 §14.5/§22 黑盒). 故: 隐数坐标让相位结构可见, 但丰度/无限仍须经分析估计, 坐标变换本身不生成存在性.

## 候选机制 (等价/直觉, 非力迫)
- **ξ 载体与能量发散链 (2026-08-26)**: §27 已落地 `xiEntire` 的整性、对称性及其与 `completedRiemannZeta`/ζ 的显式乘积关系，因而把“非平凡零点问题”压缩到整函数 ξ 的零点问题。需要注意：当前代码仍未完成“ξ 零点集无限”的 Hadamard 组合论证；临界带内 ξ=0 与 ζ=0 的双向桥也应以独立定理显式补齐，不能只凭注释中的“载体”二字视为已证。
- **能量种子 (2026-08-26, 已证前半段)**: `critical_leaf_norm_locked` 给出临界叶每项模长 `(n+1)^(-1/2)`；`critical_leaf_diagonal_energy_term` 将平方范数化为 `(n+1)^(-1)`；`critical_leaf_diagonal_energy_diverges` 证明对应调和级数不收敛。完整链条仍缺均值公式 `∫₀ᵀ|ζ(1/2+it)|²dt ≈ cT log T` 以及 Hardy 的“有限零点反证 → 无限次过零”论证。
- **log 积累的真实身份**: 对角能量的 `log N` 发散是燃料，不是引擎。它说明临界叶上的旋转项具有持续累积的二次能量，但不能单独推出干涉和 `ζ(1/2+it)` 取零；从项能量到 ζ 的均值需要交叉项控制，从均值增长到过零还需要 Hardy 论证。故“位置”(e→√e→1/2)与“丰度”(无限零点)仍是两个独立问题。
- 欧拉乘积正性 → Re s ≥ 1 无零点: 已在 §14 形式化 (zero_free_outside_envelope, mathlib riemannZeta_ne_zero_of_one_le_re)
- Bohr–Landau/Selberg → 几乎所有零点在临界线附近 (密度)
- Möbius 平方根界: RH ⟺ M(x) = O(x^{1/2+ε}) (等价)
- 机制完备环 (§13): 圆外无零点⟺零点在圆上⟺包络半径锁定⟺RH (四方向等价 — 属等价规范而非真值证明)
- 隐数坐标系幅角原理 (§16): 相位缠绕=零点数 已证为机制原子; 完整无限零点需增长估计输入
- Berry–Keating xp 量子化 (speculative)
- 有限相位抵消 — 360° 组合 (候选, 零点构造): 把 ζ(s)=0 归结为"有限个自然数的相位在 360°/整数圈对准下相消" — 有限前缀 S_N(t)=Σ_{n≤N}(n+1)^{−σ}e^{−i·t·log(n+1)} 与尾误差 R_N(t)=Σ_{n>N}(n+1)^{−σ}e^{−i·t·log(n+1)} 精确配平 ⟹ 零点。已证支撑: dirichlet_term_rotating_vector (旋转向量) + critical_leaf_norm_locked (模长锁定 n^{−1/2}) + zeta_phase_alignment_condition (无限和=0 翻译)。诚实边界: 单凭有限 S_N(t)=0 不等价 ζ=0 — 需 |R_N(t)| 受控且随 N 无界, 此"增长输入"恰是 §16/§17 已隔离的边界; 无限版需一族无界 N + 尾差估计(部分和实/虚部异号+中值定理), 即典型增长信息方向
- 频率干涉: Z(t) ≈ 2Σ n^{-1/2}cos(θ−t·log n) (Riemann–Siegel, 数值验证)
- **能量发散指标 (Hardy 方向, 2026-08-26 新候选, 种子已证)**: §11 `critical_leaf_norm_locked` (每项模长锁定 (n+1)^{-1/2}) 的未利用推论: 临界叶上每对共轭项能量 = n^{-1}, L² 能量随高度窗口 ~ log T 发散 — 固定长度的无限多根向量叠加, 其总能量不可能被有限次相位对齐吸收. 这是 Hardy 1914 定理 (临界线上无限零点) 的出发点, **同时给位置+丰度**, 且证明输入比 Riemann–von Mangoldt 弱 (不需 Stirling, 只需均值计算). 缺口: 均值公式 ∫₀ᵀ|ζ(1/2+it)|²dt ≈ Σ_{n≤T}1/n + Hardy 论证 Lean 化 (mathlib 无此均值公式, 已侦察); 另 Lindemann–Weierstrass 解析部分 mathlib 已有 (exp_polynomial_approx), §18.5 稼密性阻塞从"全缺"缩至"代数半边"
- **"角度调制生长覆盖尾项" 判定 (2026-08-25, 非力迫/被否)**: 用户主张固定基元随角度 t 生长可覆盖尾项. 不成立 — 角度 t 与指标/频率是两个独立自由度: 旋转项 §19 是 (n+1)^{-σ}·exp(-i·t·log(n+1)), t 增大只让**已有**项绕圈(相位扫描), 不能产生**新指标 n 的新频率 log(n+1) 与新权重 (n+1)^{-σ}**. 尾项 Σ_{n>M} 需一批不同频率+权重新项, t 调不出. 类似"摇一个音叉不产生第二支音高不同的音叉". "生长"若想成立必须在**频率域**(制造新 log(n) 项), 而非角度域(相位 t); 而频率域生长 = 引入新组合 = 回到证书族(§25)/多组合, 即 §18.8. 故"角度调制覆盖尾音"是死路, 频率/证书方向才是活路
- **"有限相位组合给无界高度" 退化判定 (2026-08-25, 坐标内决定性)**: 有限整数系数 log 组合 `Σ aᵢ·log(nᵢ+1)` = log(有理数), 它入 2πℤ 只可能 k=0 (因 e^{2πk}=有理数仅当 k=0, Lindemann–Weierstrass 超越性) ⟹ 所有满足 `phaseCancelRelation` 的组合**必 phaseCancelSum=0**(§18.3 退化质因数幂关系). 于是 §18.6 相位 `-t·phaseCancelSum` 恒=0, 沿整数角 t 高度恒 0, **毫无增长** — "基元对齐⟹螺旋上升无界"在定义内为假. 这是**完全在坐标系+自身组合定义内**推出的否定, 非经典框架. 唯一"无界高度"只能来自非对齐单一项随 t 转动 + 完整项/尾项, 再次到增长/存在性. 坐标系提供"高度无界"接口与语言, 但不凭空给存在性

## 图
全部 fig1–fig10 已登记于 `manifests/raw_sources.csv` (status=new)。

- fig1 `viz/fig1_projection_cross.png` 投影十字 (S/R/iR 三标签 → 复平面)
- fig2 `viz/fig2_envelope_shell.png` 三维包络壳
- fig3 `viz/fig3_critical_section.png` 临界截面
- fig4 `viz/fig4_phase_cover.png` 相位覆盖
- fig5 `viz/fig5_covering_space.png` + `viz/fig5_rollup.png` 覆盖空间 / 卷绕成圆周 |w|=√e (零点编号对应)
- fig6 `viz/fig6_winding.png` 绕数 (argument principle: 像曲线绕原点圈数 = 零点数)
- fig7 `viz/fig7_three_views.png` 三视图
- fig8 `viz/fig8_spiral_animation.gif` 螺旋动画 (万有覆盖螺旋柱面)
- fig9 `viz/fig9_mobius_walk.png` Möbius 行走
- fig10 `viz/fig10_zero_vibration.png` 频率干涉 Z(t)≈2Σn^{-1/2}cos(θ−t·log n) (Riemann–Siegel 数值)

数值验证图 (experiments/):
- `experiments/envelope_critical.png` 临界线圆周 |w|=√e 与零点共圆验证 (E1)
- `experiments/envelope_plane.png` 复平面/包络平面视图
- `experiments/envelope_surface.png` 包络曲面 w=log z (螺旋柱面/万有覆盖)

## 频率丰度机制 (2026-08-25, 新方向)
- 能量: 每项 |(n+1)^{-1/2}|² = (n+1)^{-1}, 总能量 = 调和级数 (发散)
- 临界线 = 能量临界点: Σ(n+1)^{-2σ} 收敛 ⟺ σ > 1/2; σ=1/2 处恰好发散
- 机制: 零点间距 Δγ ≈ 2π/log(γ/2π) (带宽倒数), 数值 δ̄=0.9999 (fig11)
- N(T) ≈ (T/2π)(log(T/2π) − 1) 复现, 无需 Stirling
- 已 Lean 化 (Abundance.lean, 独立模块, 无 sorry):
  freq_span_telescopes (ΣΔfreq = log(N+1) 精确) / freq_gap_le_inv /
  log_le_harmonic_sum (log(N+1) ≤ 调和和) /
  harmonic_sum_unbounded (能量无界: ∀B, ∃N, B<Σ1/(n+1) — 调和发散已证) /
  zeta_analyticAt (ζ 在 s≠1 解析) / zeta_two_ne_zero (ζ(2)≠0) /
  zeta_zero_isolated (非平凡零点孤立: identity theorem + ℂ∖{1} 连通 +
  ζ(2)≠0 排除恒零 — 零点↔ℕ 一一对应的孤立侧已证)
- 零点可枚举性完整形式化 (无 sorry): zero_set_countable (孤立 ⟹ 离散子空间
  ⟹ 第二可数 ⟹ 遗传 Lindelöf ⟹ 可数) + zero_enumeration_of_infinite
  (可数+无限 ⟹ ℕ≃zeroSet 双射, Denumerable.eqv)
- draft 全部清理: §10 HardyBridgeAssumptions (均值定理=外部输入结构体) +
  §11 FrequencyMechanismAssumptions (Riemann–Siegel 连续极限=外部输入结构体)
  + Analytic §12.4/12.5 多值 log 单值化 (exp(log w+2πi·k)=w, 叶差=2πiℤ)

- B 桥原子层内禀形式化 (Abundance §12): 临界叶能量展开 —
  rotating_integral_atom (∫e^{iΔt} 精确值) + rotating_integral_bound
  (|∫e^{iΔt}| ≤ 2/|Δ|) + diagonal_energy (∫‖v_n‖² = 2T(n+1)⁻¹ 调和)
  + cross_energy_bound (|∫v_m conj v_n| ≤ (√(m+1)√(n+1))⁻¹·2/|Δ|)
  + AlignmentEnergyBridge (B 桥声明)
- 诚实发现 (B 桥推进中): 逐项三角不等式上界在相邻频率 (Δ→0) 过粗,
  交叉相消 (Hardy–Littlewood 型 L² 论证) 是真实分析缺口, 未形式化;
  隐数坐标贡献 = 把交叉项写成旋转积分精确形态 (已证), 相消估计本身仍开放

- B1 交叉相消原子 (Abundance §12): rotating_integral_bound_min
  (|∫e^{iΔt}| ≤ min(2T, 2/|Δ|)) + log_one_add_ge_half (x/2 ≤ log(1+x))
  + near_frequency_bound (频率差 c 内含 ~m·c 项) + cross_pair_bound_min
  (每对交叉分裂上界)
- B1 数学链 (fig13 v2 数值验证): t 依赖截断 X(t)=√(t/2π) —
  E(T)/主项 → 0.5 (单侧对角 = (T/2)log(T/2π), 主项半), 交叉上界/主项
  → 0 (截断使交叉 O(√T·log T) 次主导于 T·log T) — 交叉相消机制确认;
  完整双和估计 (Hardy–Littlewood 型) 未形式化, 如实标注

- B3 隐数均值定理 (猜想 + 数值 + 部分 Lean): 单侧截断能量
  E(T) = (T/2)(log(T/2π)−1) + γ·T + o(T)
  — diagonal_integral (对角精确积分, Lean 已证, 无 Stirling) +
    harmonic_log_tendsto_euler (γ 项: 调和和 − log(N+1) → γ, Lean 已证,
    来自欧拉常数非 ζ!) + 交叉次主导 (B1) — 组装双侧重现 Hardy–Littlewood
    完整展开 T·log(T/2π) + (2γ−1)T + o(T) — 数值: E/主项 → 0.5,
    余项/T → γ ≈ 0.58 (fig13 v2)
- 诚实: 能量发散 ⟹ 零点无限 (Hardy 1914, 经典已证); 能量发散 ⟹ 丰度
  (von Mangoldt, 已证); 能量发散 ⟹ RH (位置全称) — 不能, 能量只约束
  临界线上的值大小, 不排除线外零点
