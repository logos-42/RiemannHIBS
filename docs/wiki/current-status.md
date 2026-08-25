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

# 当前状态 (2026-08-25)

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
- **缺口① (推导结论)**: `zeta_phase_alignment_condition` (§10) 用 `zeta_eq_tsum` 把 Re>1 的零点转成旋转向量和=0; 其旋转向量核 `dirichlet_term_rotating_vector` 是**复数恒等式且与 σ 无关** (可对任意 σ 用). 临界带 0<Re<1 的断路点在"级数换谐"(ζ 的 Dirichlet 展开) 而非相位机制. **正解 (已推明)**: 在临界带 `ζ(s)=0` 是良定义全纯函数取零 (`differentiableAt_riemannZeta`, s≠1), 不需级数和; "相位对齐判定" 的隐数语义 = 覆盖空间里 `expZeta_phase_principal` 把 `ζ̂(w)=ζ(log r+iθ)` — "对齐零点" 在隐数即此良定等式. 跨到经典: Re>0 用 η(交替)是 Abel 条件收敛, 排斥因子 `(1−2^{1−s})` 在临界带**恒非零** (2^{1−s}=1 只在 s=1+2πik/ln2, 实部=1, 不在 0<Re<1), 故 ζ=0⟺η=0 在临界带成立 (经典)。**真正缺口 = 条件收敛(η)+Abel/函数方程延拓 的 mathlib 工具缺失**, 非概念不可能; 落地建议 = 覆盖语义做"对齐零点"命题 + 临界带诚实标注未形式化. **状态 (2026-08-25)**: §19 已在 Re>1 落地可编译的 η 交错桥 (eta_term_rotating_vector + eta_phase_alignment_condition, 无 sorry); 临界带 0<Re<1 仍缺条件收敛 η + Abel/函数方程正则化工具, 如实标注为待形式化
- **缺口② (增长→无限零点)**: 幅角原理 (§16) + 增长分解 (§17) 已把 "N(T)→∞" 隔离为唯一缺失分析输入 — 依赖 Stirling 渐近 + 完成 ζ 有界性 (P1–P3), 二者 mathlib 均未形式化; 即使完成也只证"无限多", 不等于 RH (临界带上) — 如实标注
- 螺旋无限延伸 ≠ 全称证明: 舞台(覆盖)完备 ≠ 演员(零点)在台上
- 非平凡零点存在性与无限性: 已证仅平凡零点无限 (§15); 非平凡部分需增长阶+因子分解/幅角原理, 已有机理皆"必要条件/缺增长"型, 不携带 ζ 的增长行为, 如实标注边界

## 候选机制 (等价/直觉, 非力迫)
- 欧拉乘积正性 → Re s ≥ 1 无零点: 已在 §14 形式化 (zero_free_outside_envelope, mathlib riemannZeta_ne_zero_of_one_le_re)
- Bohr–Landau/Selberg → 几乎所有零点在临界线附近 (密度)
- Möbius 平方根界: RH ⟺ M(x) = O(x^{1/2+ε}) (等价)
- 机制完备环 (§13): 圆外无零点⟺零点在圆上⟺包络半径锁定⟺RH (四方向等价 — 属等价规范而非真值证明)
- 隐数坐标系幅角原理 (§16): 相位缠绕=零点数 已证为机制原子; 完整无限零点需增长估计输入
- Berry–Keating xp 量子化 (speculative)
- 有限相位抵消 — 360° 组合 (候选, 零点构造): 把 ζ(s)=0 归结为"有限个自然数的相位在 360°/整数圈对准下相消" — 有限前缀 S_N(t)=Σ_{n≤N}(n+1)^{−σ}e^{−i·t·log(n+1)} 与尾误差 R_N(t)=Σ_{n>N}(n+1)^{−σ}e^{−i·t·log(n+1)} 精确配平 ⟹ 零点。已证支撑: dirichlet_term_rotating_vector (旋转向量) + critical_leaf_norm_locked (模长锁定 n^{−1/2}) + zeta_phase_alignment_condition (无限和=0 翻译)。诚实边界: 单凭有限 S_N(t)=0 不等价 ζ=0 — 需 |R_N(t)| 受控且随 N 无界, 此"增长输入"恰是 §16/§17 已隔离的边界; 无限版需一族无界 N + 尾差估计(部分和实/虚部异号+中值定理), 即典型增长信息方向
- 频率干涉: Z(t) ≈ 2Σ n^{-1/2}cos(θ−t·log n) (Riemann–Siegel, 数值验证)

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
