# 理论任务文档——在验证工具上验证哈希表的C程序实现

**任务概述**
- 验证对象为哈希表的C程序实现，源文件与规格标注见 [hashtbl.c]。
- Coq 侧工具与谓词在 [hashtbl_lib.v]，手动补充的证明结论在 [hashtbl_proof_manual.v]。
- 指针数组相关的外部接口与分离策略位于 [ptr_array_def.h] 与 [ptr_array.strategies]。
- 针对哈希表结构的分离逻辑策略在 [hashtbl.strategies]。

**核心定义**
- not_key：见 [hashtbl_lib.v]
  - 定义含义：对遍历到的前缀地址集 l_prev，若映射 m 将某键 k1 映射到该前缀中的某地址 p，则 k1 必不等于目标键 k。
  - 使用场景：用于 [hashtbl.c:L125-144]的查找循环不变式，确保“尚未命中”的前缀不包含目标键，避免错误匹配。

**辅助更新算子**
- update_b0_at / update_nth / update_nth_Z：见 [hashtbl_lib.v:L198-212]  
  - 作用说明：update_b0_at 用于“在索引 ind 处替换桶头与其链表”；update_nth 与 update_nth_Z 为列表第 n 项替换的通用与整数下标版本。
  - 使用场景：配合桶表示 b0 与头数组 lh 的抽象更新，支撑LRU调整或清理时的“状态镜像”一致性。

**新增引理**
- sllseg_nil_emp：见 [hashtbl_lib.v:L715-L719] 
  - 结论说明：空的单向链表片段 sllseg p p nil 蕴含 emp，用于闭合空段不变式。
- b_sll / sll_b：见 [hashtbl_lib.v:L721-L740]  
  - 结论说明：在 store_map(store_sll, b) 与“缺失索引”的视图之间分割/合并，便于对特定桶 i 的局部推理。
- sllseg_head：见 [hashtbl_lib.v:L743-L760]  
  - 结论说明：当尾指针 q 为 NULL 时，sllseg p q l 推出“l 为空或 p 属于 l”，用于定位片段头节点。
- ptr_string_name：见 [hashtbl_lib.v:L763-L774]
  - 结论说明：从结构体域 &(p_current->key) 与其字符串存储，导出抽象的 store_name，桥接指针域与键名谓词。

**MapLib 扩展**
- store_map_missing_first_i_Z：见 [MapLib.v:L36-L61]
  - 定义含义：自索引 i 起，对 m 中“存在值且索引≥i”的键集合进行迭代分离组合，得到按 P 的视图。
  - 相关引理（均为整体使用说明，证明细节在工程中以策略/自动化处理）：  
    - store_map_missing_first_i_split：从 i 分离出 i+1 之后的集合，并析出当前位置的断言 P i b。  
    - store_map_missing_i_equiv_store_map_first_i：与既有 store_map_missing_i 在0起点的等价关系。  
    - store_map_missing_first_i_empty：在边界处（如 i=210）得到空视图，用于循环结束收尾。
  - 使用场景：服务于 [hashtbl.c:L346-L365] 的清理循环不变式，表达“已处理前缀/待处理后缀”的分离结构。

**PtrArray 接口与策略**
- 外部断言接口：见 [ptr_array_def.h]  
  - 关键断言：PtrArray::full、PtrArray::missing_i、PtrArray::ceil 及其形状断言，配合 Znth/replace_Znth 构造逐项推理。
- 分离策略：见 [ptr_array.strategies]  
  - 主要规则说明：  
    - 从 full 抽取到某下标数据并转换为 missing_i（id:1），以及将 missing_i 与该位置 data_at 合并回 full（id:2/3）。  
    - ceil 片段的抽取与拼接（id:7/8/9/10/11/12），支撑区间级别的数组段推理。  
  - 使用场景：定位桶数组 h->bucks[ind] 的元素访问与更新，确保数组与抽象列表 lh 的一致性。

**哈希表分离策略**
- 见 [hashtbl.strategies]  
  - sll/dll 结构的展开与折叠（如 unfold_sll/fold_sll、unfold_dll/fold_dll），支撑链表遍历与LRU维护。  
  - sllseg/sllbseg 到空段或整体段的转换（id:9/10/11/12/25/26），简化边界与拼接场景。  
  - 键名与结构体字段的桥接策略，辅助从 data_at 转到高层谓词关系。

**C 程序与规格对应**
- hashtbl_findref：见 [hashtbl.c:L97-L188]  
  - 规格要点：在查找循环中维持“b0(ind) 的桶分解”“sllbseg 前缀与 sll 后缀”“not_key 保证未命中前缀无目标键”等不变式；命中后执行LRU，将节点移至桶头，并返回 &val。
- hashtbl_remove：见 [hashtbl.c:L190-L291]  
  - 规格要点：遍历定位目标节点，维护 dll 顶端与相邻指针一致性（up/down互指修复），更新桶链表并释放节点；返回旧值并设置 removed。
- hashtbl_clear：见 [hashtbl.c:L319-L374]  
  - 规格要点：对 0..210 的桶进行逐一清理，循环不变式使用 PtrArray::missing_i 与 store_map_missing_first_i_Z 描述“已清理与未清理”的区段；循环结束后释放数组并置空。
- hashtbl_free_blist：见 [hashtbl.c:L293-L317]  
  - 规格要点：递归释放单链表，使用 sll 展开得到后继与键名存储，再逐步释放字符串与节点。

**连续次要证明整体说明**
- 结构性拆分与合并：针对 sll/sllseg/dllseg 的展开-折叠、片段到整体的拼接，均通过策略与基础引理实现自动化或短证明。
- 映射视图步进：store_map 与“缺失索引”视图之间的分割/合并（b_sll/sll_b），以及数组区段视图的步进（PtrArray 规则），统一用于循环体的推进。
- 键名桥接：ptr_string_name 等将结构体域与抽象键名谓词关联，减少在字符串比较与命中分支处的低层细节。
- 边界收尾：sllseg_nil_emp 与 MapLib 空视图引理用于循环结束或空段处理的收尾，避免无谓展开。

**小结论列表**
- sllseg_nil_emp：空段即 emp，用于边界闭合。
- sllseg_head：q=NULL 的片段，其头指针 p 要么为空要么属于 l。
- b_sll / sll_b：store_map 在索引 i 的分割与合并，隔离桶内局部证明。
- ptr_string_name：&(p->key) 与 store_string 推出 store_name，桥接字段到抽象键名。
- update_b0_at：替换 b0(ind) 的头与链表，镜像桶头变更。
- update_nth / update_nth_Z：列表第 n 项替换及其整形索引版本。
- store_map_missing_first_i_Z 相关引理：用于从 i 起的区段步进、与旧视图的等价、以及边界处的空视图。
