---
dataset_info:
  features:
  - name: uuid
    dtype: string
  - name: problem
    dtype: string
  - name: question_type
    dtype: string
  - name: answer
    dtype: string
  - name: author
    dtype: string
  - name: formal_statement
    dtype: string
  - name: formal_ground_truth
    dtype: string
  - name: ground_truth_type
    dtype: string
  - name: formal_proof
    dtype: string
  - name: rl_data
    struct:
    - name: n_correct_proofs
      dtype: int64
    - name: n_proofs
      dtype: int64
    - name: win_rate
      dtype: float64
  - name: source
    dtype: string
  - name: problem_type
    dtype: string
  - name: exam
    dtype: string
  splits:
  - name: train
    num_bytes: 171546775
    num_examples: 104155
  download_size: 78426425
  dataset_size: 171546775
configs:
- config_name: default
  data_files:
  - split: train
    path: data/train-*
license: apache-2.0
---




# Dataset Card for NuminaMath-LEAN

![image/png](https://cdn-uploads.huggingface.co/production/uploads/621660534b06824e1e5022ed/YrcCZYcgVEtKoRmN2sLVR.png)

## Dataset Summary
NuminaMath-LEAN is a large-scale dataset of 100K mathematical competition problems formalized in Lean 4. It is derived from a challenging subset of the [NuminaMath 1.5](https://huggingface.co/datasets/AI-MO/NuminaMath-1.5) dataset, focusing on problems from prestigious competitions like the IMO and USAMO. It represents the largest collection of human-annotated formal statements and proofs designed for training and evaluating automated theorem provers. This is also the dataset behind our [Kimina-Prover 72B](https://huggingface.co/blog/AI-MO/kimina-prover).

## Acknowledgment
We thank all the annotators who have participated in building this dataset. We are also very grateful to the whole Lean 4 community for the priceless help.

## Data description

`problem`, `question_type`, `answer`, `source`, `problem_type` are identical to those in the NuminaMath 1.5

- `author`: the author of formal statement, `autoformalizer` if the statement is formalised by our autoformalizer model, `human` when it is formalised by an annotator.

- `formal_statement`: formal statement in lean 4 of the problem. It is written in a similar way as miniF2F.

- `formal_ground_truth`: the formal proof of the problem written by a human annotator. It is available only when `author == human`.

- `ground_truth_type`: a field to describe the annotation status of `formal_ground_truth`
    - `complete`: this means the formal proof is complete.
    - `with_sorry`: this means the formal proof is written with some `sorry` in certain `have` statements.
    - `statement`: only the statement has been formalised. Proof is filled only with a `sorry`

- `formal_proof`: the formal proof written by our [model](https://huggingface.co/AI-MO/Kimina-Prover-72B) during RL training. It is available only if the model manage to prove it, otherwise it is empty.

- `rl_data`: a dict containing some information during the RL training.
    - `n_proofs`: The number of times this problem is shown to the model. 0 means the problem has never been shown to the model.
    - `n_correct_proofs`: The number of times the model managed to solve this problem.
    - `win_rate`： `n_correct_proofs / n_proofs`

## Method

We have selected the most challenging part of the NuminaMath 1.5 dataset. Namely, we have removed `cn_k12` and other non math competition problems. We then filter out `geometry` and `combinatorics` problems, because of their difficulty of formalization, to create the final subset.

We have also augmented the original NuminaMath 1.5 by adding the subset `olympiads-ref`, where problems are collected from most challenging competition problems such as IMO, IMO shortlist, USAMO etc. The solution and the final answer have been carefully curated from the official PDF.


## Compatibility
All formalizations in this dataset are written in Lean 4 and are compiled and verified against mathlib v4.15.0. Users should ensure their environment matches this dependency to guarantee compatibility and prevent compilation errors.


## Limitation
- missing metadata. Some metadata is missing, especially for newly added problems. For example, a lot of human annotated problem do not have `question_type`. This will be fixed very soon.

- incorrect reference answer. During the formalization process, we realised that sometimes the reference answer is wrongly extracted. We have not done the reverse process of correcting the reference answer yet.

- inaccurate statement formalization. Limited computational resources were used to prove the negation or the contradiction of the problems.  We have discovered some wrongly formalized problems (mainly due to the limitations of our autoformalizer). We will release a better version of the formal statement very soon.

## Licensing Information
The dataset is available under the Apache License, Version 2.0.

## Citation Information
```
@article{kimina_prover_2025,
    title = {Kimina-Prover Preview: Towards Large Formal Reasoning Models with Reinforcement Learning},
    author = {Wang, Haiming and Unsal, Mert and Lin, Xiaohan and Baksys, Mantas and Liu, Junqi and Santos, Marco Dos and Sung, Flood and Vinyes, Marina and Ying, Zhenzhe and Zhu, Zekai and Lu, Jianqiao and Saxcé, Hugues de and Bailey, Bolton and Song, Chendong and Xiao, Chenjun and Zhang, Dehao and Zhang, Ebony and Pu, Frederick and Zhu, Han and Liu, Jiawei and Bayer, Jonas and Michel, Julien and Yu, Longhui and Dreyfus-Schmidt, Léo and Tunstall, Lewis and Pagani, Luigi and Machado, Moreira and Bourigault, Pauline and Wang, Ran and Polu, Stanislas and Barroyer, Thibaut and Li, Wen-Ding and Niu, Yazhe and Fleureau, Yann and Hu, Yangyang and Yu, Zhouliang and Wang, Zihan and Yang, Zhilin and Liu, Zhengying and Li, Jia},
    year = {2025},
    url = {http://arxiv.org/abs/2504.11354},
}
```