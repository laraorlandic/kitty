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
#include <algorithm> 
#include <iostream>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "bit_operations.hpp"
#include "implicant.hpp"
#include "print.hpp"

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
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;

  /*Check unateness of all variables*/
  auto numvars = tt.num_vars();

  std::vector<uint8_t> neg_unate_vars;



  //Loop through all variables checking unatness and 
  for ( uint8_t i = 0; i < numvars; i++ )
  {
    Unateness un;
    un = is_unate( tt, i );
    //If the function is binate on any variable --> Non-TF
    if ( un == BINATE )
    {
      return false;
    }
    else if ( un == NEGATIVE )
    {
      neg_unate_vars.push_back( i );
    }
  
  }
  

  // Make sure f is unate by substituting x with x'
  TT f_star;
  f_star = tt;


  
  for ( auto i : neg_unate_vars )
  {
      flip_bit( f_star, (uint64_t)i );
  }
  

  //Get prime implicants of on set
  std::vector<cube> prime_implicants_on_set;
  prime_implicants_on_set = get_prime_implicants_morreale( f_star );

  //Get prime implicants of off set
  std::vector<cube> prime_implicants_off_set;
  prime_implicants_off_set = get_prime_implicants_morreale( unary_not( f_star ) );

  //Set up ILP
  int n_vars_ILP = numvars + 1; //# of vars to solve for = number of literals + 1 for T
  lprec* lp;
  int row_counter = 0;
  int col_counter = 0;
  lp = make_lp( 0, n_vars_ILP ); //initialize model

  //Initial constraints: w_1, w_2 ... w_n, T >= 0
  for ( uint8_t i = 0; i < n_vars_ILP; i++ )
  {
    double* row = new double[n_vars_ILP+1];
    for ( int j = 1; j <= n_vars_ILP; j++ )
    {
      row[j] = 0.0;
    }
    row[i+1] = 1.0;
    add_constraint( lp, row, GE, 0 );
  }

  write_lp( lp, "model_1.lp" );

  //Add ILP rows for on set
  //For each variable xi in cube C, add constraint sum(w_i) - T >= 0
  set_add_rowmode( lp, TRUE );
  for ( int c = 0; c < prime_implicants_on_set.size(); c++ )
  {
    double* row = new double[n_vars_ILP+1];
    cube C = prime_implicants_on_set.at( c );
    for ( uint8_t i = 0; i < numvars; i++ )
    {
      //Find whether a variable is part of a cube or not
      bool cube_mask = C.get_mask(i);
      bool polarity = C.get_bit( i );
      if ( cube_mask & polarity)
      {
        row[i+1] = 1.0; //variable xi is part of cube C
      }
      else
      {
        row[i+1] = 0.0; //variable xi is not part of cube C
      }
    }
    row[n_vars_ILP] = -1.0; //constant of T variable is -1
    add_constraint( lp, row, GE, 0 );
  }

  write_lp( lp, "model_2.lp" );

  //Add ILP rows for off set
  //For each variable xi' not in cube C, add constraint sum(w_i) - T <= -1
  set_add_rowmode( lp, TRUE );
  for ( int c = 0; c < prime_implicants_off_set.size(); c++ )
  {
    double* row = new double[n_vars_ILP+1];
    cube C = prime_implicants_off_set.at( c );
    for ( uint8_t i = 0; i < numvars; i++ )
    {
      //Find whether a variable is part of a cube or not
      bool cube_mask = C.get_mask( i );
      bool polarity = C.get_bit( i );
      if ( (cube_mask) & (!polarity)  )
      {
        row[i+1] = 0.0; //variable xi' is part of cube C
      }
      else
      {
        row[i+1] = 1.0; //variable xi' is not part of cube C
      }
    }
    row[n_vars_ILP] = -1.0; //constant of T variable is -1
    add_constraint( lp, row, LE, -1 );
  }

  //Construct ILP objective: minumum of w_1 + w_2 + ... w_n + T
  set_add_rowmode( lp, FALSE );
  double* row = new double[n_vars_ILP+1];
  for ( int i = 1; i <= n_vars_ILP; i++ )
  {
    row[i] = 1;
  }
  set_obj_fn( lp, row );
  set_minim( lp );

  write_lp( lp, "model.lp" );

  //Solve LP
  int result = solve( lp );
  //Unable to solve model --> not TF
  if ( result != 0 )
  {
    return false;
  }
  get_variables( lp, row );
  for ( int i = 0; i < n_vars_ILP; i++ )
  {
    linear_form.push_back( (int64_t)row[i] );
  }

  //Correct for substituted variables
  for ( auto i : neg_unate_vars )
  {
    linear_form[i] = -linear_form[i];
    linear_form[n_vars_ILP - 1] = linear_form[n_vars_ILP - 1] + linear_form[i];
  }

  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  if ( plf )
  {
    *plf = linear_form;
  }
  return true;
}

enum Unateness
{
  NEGATIVE = 0,
  POSITIVE = 1,
  BINATE = 2
};

template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
//Check if truth table tt is unate on variable var
Unateness is_unate( const TT& tt, uint8_t var)
{
  auto numvars = tt.num_vars();
  auto const tt1 = cofactor0( tt, var );
  auto const tt2 = cofactor1( tt, var );

  uint8_t table_size = (2 << ( numvars - 1 ));
  std::vector<int> pos_un_vec( table_size, 0 ); 
  std::vector<int> neg_un_vec( table_size, 0 ); 

  for ( auto bit = 0; bit < table_size ; bit++ )
  {
    //Is negative cofactor contained in positive cofactor?
    if ( get_bit( tt1, bit ) <= get_bit( tt2, bit ) )
    {
      pos_un_vec.at( bit ) = 1;
    }
    //Is positive cofactor contained in negative cofactor?
    if ( get_bit( tt2, bit ) <= get_bit( tt1, bit ) )
    {
      neg_un_vec.at( bit ) = 1;
    }
  }

  //If all negative cofactors are contained in the positive cofactor --> Positive Unate
  if ( std::all_of( pos_un_vec.begin(), pos_un_vec.end(), []( int i ) { return i == 1; } ) )
  {
    return POSITIVE;
  
  }
  //If all positive cofactors are contained in the negative cofactor --> Negative Unate
  else if ( std::all_of( neg_un_vec.begin(), neg_un_vec.end(), []( int i ) { return i == 1; } ) )
  {
    return NEGATIVE;
  }
  //Else: binate
  else
  {
    return BINATE;
  }
}

} /* namespace kitty */
