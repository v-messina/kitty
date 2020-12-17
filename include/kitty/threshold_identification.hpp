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


enum Constraint_Type { G_E, L_E, E };   /* G_E >=; L_E <=; E == */

struct Constraint {
  std::vector<int64_t> weight;
  Constraint_Type type;
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

  \param tt_fstar The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt_copy` if it is a TF.
             The linear form has `tt_copy.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt_copy` is a TF; `false` if `tt_copy` is a non-TF.
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

  auto ONSET = get_prime_implicants_morreale( tt_copy );
  auto tt_neg = unary_not( tt_copy );
  auto OFFSET = get_prime_implicants_morreale(tt_neg);

  std::vector<Constraint> constraints;

  for (auto& cube_i : ONSET){
    Constraint constraint;
    for(uint64_t var_i = 0; var_i < n_var; var_i++){
      if (cube_i.get_mask(var_i) == 1){
        if(cube_i.get_bit(var_i) == 1){
          constraint.weight.emplace_back(1);
        }
        else{
          constraint.weight.emplace_back(0);
        }
      }
      else{
        constraint.weight.emplace_back(0);
      }
    }
    constraint.weight.emplace_back(-1);
    constraint.type = G_E;
    constraint.constant = 0;
    constraints.emplace_back(constraint);
  }

  for (auto& cube_i : OFFSET){
    Constraint constraint;
    for(uint64_t var_i = 0; var_i < n_var; var_i++){
      if (cube_i.get_mask(var_i) == 0){
        constraint.weight.emplace_back(1);
      }
      else{
        constraint.weight.emplace_back(0);
      }
    }
    constraint.weight.emplace_back(-1);
    constraint.type = L_E;
    constraint.constant = -1;
    constraints.emplace_back(constraint);
  }

  /*Positive weights*/
  for(uint64_t var_i = 0; var_i <= n_var; var_i++){
    Constraint constraint;
    for(uint64_t i = 0; i <= n_var; i++){
      constraint.weight.emplace_back(0);
    }
    constraint.weight[var_i] = 1;
    constraint.constant = 0;
    constraint.type = G_E;
    constraints.emplace_back(constraint);
  }

  /* lp_solve */
  lprec *lp;
  auto n_rows = constraints.size();
  std::vector<double> row;

  /* Create a new LP model */
  lp = make_lp(0, n_var+1);
  if(lp == nullptr) {
    fprintf(stderr, "Unable to create new LP model\n");
    return(false);
  }

  set_add_rowmode(lp, TRUE);

  /*the objective function*/
  row.emplace_back(1.0);
  for(uint64_t col = 1; col<=n_var+1; col++){
    row.emplace_back(1.0);
  }

  set_obj_fn(lp, row.data());

  for(uint64_t rows = 0; rows < n_rows; rows++){
    for(uint64_t col = 1; col <= n_var+1; col++){
      row[col] = constraints[rows].weight[col-1];
    }
    if(constraints[rows].type == G_E)
      add_constraint(lp, row.data(), GE, constraints[rows].constant);
    else if (constraints[rows].type == L_E)
      add_constraint(lp, row.data(), LE, constraints[rows].constant);
  }

  set_add_rowmode(lp, FALSE);
  set_minim(lp);
  print_lp(lp);
  set_verbose(lp, IMPORTANT);

  for(auto i = 1u; i< n_var+1; i++){
    set_int(lp, i, TRUE);
  }

  int ret = solve(lp);
  if(ret == OPTIMAL){    //tt_copy is TF
    /* objective value */
    printf("Objective value: %f\n", get_objective(lp));

    /* variable values */
    get_variables(lp, row.data());

    int threshold = row[n_var];

    for(uint64_t i = 0; i < n_var; i++){
      if( neg_var[i] )
      {
        linear_form.emplace_back(-row[i]);
        threshold = threshold - row[i];
      }
      else
        linear_form.emplace_back(row[i]);
    }
    linear_form.emplace_back(threshold);

    /*print values*/
    for(uint64_t j = 0; j <= n_var +1; j++){
      printf( "%s: %f\n", get_col_name( lp, j + 1 ), row[j] );
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

