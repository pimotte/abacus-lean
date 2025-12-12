# Abacus

*Working title, official name pending*

Formal math library designed to facilitate the use of proof assistants in first-year mathematics education. Specifically for the [Lean](https://lean-lang.org/) proof assistant.

## Key features (WIP)
- ### Single, unified type `Number` for numbers

  As introduced by Yves Bertot in [one_num_type](https://github.com/ybertot/one_num_type). Also adopted by [Yalep](https://gricad-gitlab.univ-grenoble-alpes.fr/yalep/Yalep).

- ### Limits as (potentially ill-defined) functions

  Allows for using limits in chains of equalities, like
  
  > `lim n, (a n + b n) = (lim n, a n) + (lim n, b n) = p + q`

  given that `(lim n, a n) = p` and `(lim n, b n) = q`



## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
