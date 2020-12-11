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
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"

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

  std::vector<int32_t> neg_unate_vars;

  //Loop through all variables checking unatness and 
  for ( int32_t i = 0; i < numvars; i++ )
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
Unateness is_unate( const TT& tt, uint32_t var)
{
  auto numvars = tt.num_vars();
  auto const tt1 = cofactor0( tt, var );
  auto const tt2 = cofactor1( tt, var );

  uint32_t table_size = (2 << ( numvars - 1 ));
  vector<int> pos_un_vec( table_szie, 0 ); 
  vector<int> neg_un_vec( table_szie, 0 ); 

  for ( auto bit = 0; bit < table_size ; bit++ )
  {
    if ( get_bit( tt1, bit ) <= get_bit( tt2, bit ) )
    {
      pos_un_vec.at( bit ) = 1;
    }
    else if ( get_bit( tt2, bit ) <= get_bit( tt1, bit ) )
    {
      neg_un_vec.at( bit ) = 1;
    }
  }

  if ( std::all_of( pos_un_vec.begin(), pos_un_vec.end(), []( int i ) { return i == 1; } ) )
  {
    return POSITIVE;
  
  }
  else if ( std::all_of( neg_un_vec.begin(), neg_un_vec.end(), []( int i ) { return i == 1; } ) )
  {
    return NEGATIVE;
  }
  else
  {
    return BINATE;
  }
}

} /* namespace kitty */
