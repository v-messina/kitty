/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once


#include <vector>
#include <fstream>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "bit_operations.hpp"
#include "cube.hpp"
#include "dynamic_truth_table.hpp"
#include "implicant.hpp"
#include "operations.hpp"
#include "static_truth_table.hpp"
#include "traits.hpp"

struct Constraint {
  std::vector<int64_t> variable_weight;
  int constant; /* the right-hand side constant */
};

namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/

template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold(const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;

  auto tt_copy = tt;

  /* Saving the number of variables and the number of bits of the tt_copy in variables */
  uint64_t n_var = tt_copy.num_vars();
  uint64_t n_bit = tt_copy.num_bits();

  /* Flags to detect the presence of binate or negative unate tt_copy */
  bool is_neg = false;
  bool is_pos = false;

  std::vector<bool> neg_var;

  /* Filtering the binate tt_copy and the negative unte tt_copy */
  /* Cycle on the different variables of the function */
  for (uint64_t var_i = 0u; var_i < n_var; var_i++){

    auto const tt_neg = cofactor0( tt_copy, var_i);
    auto const tt_pos = cofactor1( tt_copy, var_i);

    /* Cycle on all the bits of the tt_copy */
    for(uint64_t i = 0u; i < n_bit; i++){

      if (get_bit(tt_pos, i) < get_bit(tt_neg, i))
        is_neg = true;

      if (get_bit(tt_pos, i) > get_bit(tt_neg, i))
        is_pos = true;
    }

    /* tt_copy is binate, so it is not a TF */
    if( is_pos && is_neg )
      return false;

    /* Check if the tt_copy is negative unate in variable "var_i" */
    if( !is_pos && is_neg )
      /* Construction of f*, considering "var_i" negate */
      flip_inplace( tt_copy, var_i );

    neg_var.emplace_back(!is_pos && is_neg);

    is_pos = false;
    is_neg = false;

  }

  /* Computing ONSET and OFFSET */
  auto ONSET = get_prime_implicants_morreale( tt_copy );
  auto tt_neg = unary_not( tt_copy );
  auto OFFSET = get_prime_implicants_morreale(tt_neg);

  std::vector<Constraint> constraints;

  /* Creating constraints */
  for (auto& cube_i : ONSET){
    Constraint constraint;
    for(uint64_t var_i = 0; var_i < n_var; var_i++){
      if (cube_i.get_mask(var_i) == 1){
        constraint.variable_weight.emplace_back(cube_i.get_bit(var_i));
      }
      else{
        constraint.variable_weight.emplace_back(0);
      }
    }
    constraint.variable_weight.emplace_back(-1);
    constraint.constant = 0;
    constraints.emplace_back(constraint);
  }

  for (auto& cube_i : OFFSET){
    Constraint constraint;
    for(uint64_t var_i = 0; var_i < n_var; var_i++){
      constraint.variable_weight.emplace_back(!cube_i.get_mask(var_i));
    }
    constraint.variable_weight.emplace_back(-1);
    constraint.constant = -1;
    constraints.emplace_back(constraint);
  }

  /* Adding positive variable weights */
  for(uint64_t var_i = 0; var_i <= n_var; var_i++){
    Constraint constraint;
    for(uint64_t i = 0; i <= n_var; i++){
      if (i == var_i)
        constraint.variable_weight.emplace_back(1);
      else
        constraint.variable_weight.emplace_back(0);
    }
    constraint.constant = 0;
    constraints.emplace_back(constraint);
  }

  /* lp_solve */
  lprec *lp;
  auto n_rows = constraints.size();
  std::vector<double> rows;

  /* Creating a new LP model */
  lp = make_lp(0, n_var+1);
  if(lp == nullptr) {
    fprintf(stderr, "Unable to create new LP model\n");
    return(false);
  }

  /* Setting rowmode to pass one row each time */
  set_add_rowmode(lp, TRUE);

  for(uint64_t col = 0; col<=n_var+1; col++){
    rows.emplace_back(1.0);
  }

  /* Setting the objective function */
  set_obj_fn(lp, rows.data());

  /* Adding constraints */
  for(uint64_t row = 0; row < n_rows; row++){
    for(uint64_t col = 1; col <= n_var+1; col++){
      rows[col] = constraints[row].variable_weight[col-1];
    }
    if(constraints[row].constant == 0)
      add_constraint(lp, rows.data(), GE, constraints[row].constant);
    else if (constraints[row].constant == -1)
      add_constraint(lp, rows.data(), LE, constraints[row].constant);
  }

  set_add_rowmode(lp, FALSE);
  /* Minimizing mode */
  set_minim(lp);
  print_lp(lp);
  set_verbose(lp, IMPORTANT);

  for(auto i = 1u; i < n_var+1; i++){
    set_int(lp, i, TRUE);
  }

  /* Solving the LP */
  int ret = solve(lp);
  /* if OPTIMAL means that tt_copy is a TF */
  if(ret == OPTIMAL){
    printf("Objective value: %f\n", get_objective(lp));

    /* Getting weights found */
    get_variables(lp, rows.data());

    /* Getting threshold found */
    int T = rows[n_var];

    /* Setting weights and threshold considering the negated variables */
    for(uint64_t i = 0; i < n_var; i++){
      if( neg_var[i] ){
        linear_form.emplace_back(-rows[i]);
        T = T - rows[i];
      }
      else
        linear_form.emplace_back(rows[i]);
    }
    linear_form.emplace_back( T );

    /* Printing values */
    for(uint64_t j = 0; j <= n_var +1; j++){
      printf( "%s: %f\n", get_col_name( lp, j + 1 ), rows[j] );
    }
  }
  else
    return false;

  if ( plf ){
    *plf = linear_form;
  }
  return true;
}

} /* namespace kitty */

