/*!
  \file aig_algebraic_rewriting.hpp
  \brief AIG algebraric rewriting

  EPFL CS-472 2021 Final Project Option 1
*/

#pragma once

#include "../networks/aig.hpp"
#include "../views/depth_view.hpp"
#include "../views/topo_view.hpp"

namespace mockturtle
{

namespace detail
{

template<class Ntk>
class aig_algebraic_rewriting_impl
{
  using node = typename Ntk::node;
  using signal = typename Ntk::signal;

public:
  aig_algebraic_rewriting_impl( Ntk& ntk )
    : ntk( ntk )
  {
    static_assert( has_level_v<Ntk>, "Ntk does not implement depth interface." );
  }

  void run()
  {
    bool cont{true}; /* continue trying */
    while ( cont )
    {
      cont = false; /* break the loop if no updates can be made */
      ntk.foreach_gate( [&]( node n ){
        if ( try_algebraic_rules( n ) )
        {
          ntk.update_levels();
          cont = true;
        }
      });
    }
  }

private:


  /* Try various algebraic rules on node n. Return true if the network is updated. */
  bool try_algebraic_rules( node n )
  {
    if ( try_associativity( n ) )
      return true;
    if ( try_distributivity_or( n ) )
      return true;
    if ( try_distributivity_and( n ) )
      return true;
    if ( try_3_layer( n ) )
      return true;
    /* if ( try_absorption_and( n ) )
       return true;*/
    return false;
  }

 

  /* ------------------------------------------------------------------------------------------------------ */


  bool try_absorption_and( node n )
  {
    std::vector <node> children_n;
    std::vector <signal> children_s;
    ntk.foreach_fanin(n, [&](signal s){
    node child = ntk.get_node( s );     
    children_n.push_back(child);
    children_s.push_back( s );});
    
    node child_1 = children_n.at(0);
    node child_2 = children_n.at(1);
    signal sign_1 = children_s.at(0);
    signal sign_2 = children_s.at(1);

    if (ntk.is_constant(child_1))
    {
        if (ntk.constant_value(child_1) == false)
        {
            ntk.substitute_node( n, sign_1 );
            return true;
        }
        else 
        {
          ntk.substitute_node( n, sign_2 ); 
            return true;
        }
    }
    else if (ntk.is_constant(child_2))
    {
        if (ntk.constant_value(child_2) == false)
        {
            ntk.substitute_node( n, sign_2 );
            return true;
        }
        else 
        {
            ntk.substitute_node( n, sign_1 );
            return true;
        }
    }
    else if (sign_1 == sign_2)
    {
        ntk.substitute_node( n, sign_1 );
        return true;
    }
    /* else if ( !( sign_1 ) == sign_2 )
    {
        ntk.substitute_node(n, segnale 0);
        return true;
    } */
    else return false;
  } 

  /* ------------------------------------------------------------------------------------------------------ */

   /* swap function for associativity */

  void a_swap (signal a, signal b, signal c, node n1, node n2)
  {
    signal d_first = ntk.create_and( a, b );
    signal e_first = ntk.create_and( c, d_first );
    ntk.substitute_node( n1, e_first );
  }

  /* Try the associativity rule on node n. Return true if the network is updated. */
  bool try_associativity( node n )
  {
    if ( !ntk.is_on_critical_path( n ) )
      return false;
    else
    {
      std::vector<node> children_n;
      std::vector<signal> children_s;
      ntk.foreach_fanin( n, [&]( signal const& s )
                         {
                           node child = ntk.get_node( s );
                           children_n.push_back( child );
                           children_s.push_back( s );
                         } );

      if ( ntk.level( children_n[0] ) > ntk.level( children_n[1] ) )
      {
        std::swap( children_n[0], children_n[1] ); //children[1] adesso è vecchio children 0, ossia il critico
        std::swap( children_s[0], children_s[1] ); //quindi children[1] è sempre il critico
      }
      else if ( ntk.level( children_n[0] ) == ntk.level( children_n[1] ) )
        return false;

     node child_critical = children_n[1];
     node child_not_critical = children_n[0];
     signal signal_crit_child = children_s[1];
     signal signal_not_cri_child = children_s[0];

     std::vector<node> children_crit_n;
     std::vector<signal> children_crit_s;
     ntk.foreach_fanin( child_critical, [&]( signal const& f )
                        {
                          node granchild = ntk.get_node( f );
                          children_crit_n.push_back( granchild );
                          children_crit_s.push_back( f );
                        } );

     if ( ntk.level( children_crit_n[0] ) > ntk.level( children_crit_n[1] ) )
     {
       std::swap( children_crit_n[0], children_crit_n[1] );
       std::swap( children_crit_s[0], children_crit_s[1] ); 
     }
     else if ( ntk.level( children_crit_n[0] ) == ntk.level( children_crit_n[1] ) )
       return false;

     node critical_granchild = children_crit_n[1];
     signal critical_granchild_signal = children_crit_s[1];
     node not_critical_granchild = children_crit_n[0];
     signal not_critical_granchild_signal = children_crit_s[0];

     if ( ntk.level( critical_granchild ) > ntk.level( child_not_critical ) && !ntk.is_complemented( signal_crit_child ) )
     {
       signal d_first = ntk.create_and( signal_not_cri_child, not_critical_granchild_signal );
       signal e_first = ntk.create_and( critical_granchild_signal, d_first );
       ntk.substitute_node( n, e_first );
       return true;
     }
     else
       return false;

    }
  }

  /* ------------------------------------------------------------------------------------------------------ */

  /* Try the distributivity rule on node n. Return true if the network is updated. */

  bool try_distributivity_or( node n )
  {
    if ( !ntk.is_on_critical_path( n )) //se il nodo non è sul critical path skippa
      return false;
    else
    {
      bool flag = false;
      std::vector<node> children_n;
      std::vector<signal> children_s;
      ntk.foreach_fanin( n, [&]( signal const& s )
                         {
                           node child = ntk.get_node( s );
                           children_n.push_back( child );
                           children_s.push_back( s );
                           //figli sul crit path e complementati
                           if ( !ntk.is_on_critical_path( child ) || !ntk.is_complemented( s ) )
                             flag = true;
                         } );

      if (flag || children_n.size() < 2)
        return false;

      node child_1 = children_n.at(0);
      node child_2 = children_n.at(1);

      bool exist = false;
      signal comune;
      ntk.foreach_fanin( child_1, [&]( signal const& f )
                         {
                           signal granchild1 = f;
                             ntk.foreach_fanin( child_2, [&]( signal const& s ) {
                                 signal granchild2 = s;
                                 // il nipote comune deve stare sul critical path
                                 if ( granchild1 == granchild2 && ntk.is_on_critical_path(ntk.get_node(granchild1)))
                                 {
                                   exist = true;
                                   comune = granchild1;     
                                 }
                             } );
                         } );

      if ( !exist )
        return false;


      std::vector<signal> diversi;

      ntk.foreach_fanin( child_1, [&]( signal const& z )
                         {
                           if ( (comune != z) && !ntk.is_on_critical_path(ntk.get_node(z)))
                             diversi.push_back( z );
                         } );

      ntk.foreach_fanin( child_2, [&]( signal const& w )
                         {
                           if ( (comune != w) && !ntk.is_on_critical_path(ntk.get_node(w)))
                             diversi.push_back( w );
                         } );


      if ( diversi.size() == 2 ) //nessuno è un PI o non è il caso (A+B) + (A+B)
      {
        signal not_critical = ntk.create_and( !diversi.at(0), !diversi.at(1) );
        signal new_output = ntk.create_and( comune, !not_critical );
        ntk.substitute_node( n, !new_output );
        return true;
      }
      else
          return false;
    }
  }     


    /* ------------------------------------------------------------------------------------------------------ */


  /* Try the distributivity rule on node n. Return true if the network is updated. */

  bool try_distributivity_and( node n )
  {
    if ( !ntk.is_on_critical_path( n ) ) //se il nodo non è sul critical path skippa
      return false;
    else
    {
    bool flag = false;
    std::vector<node> children_n;
    std::vector<signal> children_s;
    ntk.foreach_fanin( n, [&]( signal const& s )
                       {
                         node child = ntk.get_node( s );
                         children_n.push_back( child );
                         children_s.push_back( s );
                         //figli sul crit path e complementati
                         if ( !ntk.is_on_critical_path( child ) || ntk.is_complemented( s ) )
                           flag = true;
                       } );

    if ( flag || children_n.size() < 2 )
      return false;

    node child_1 = children_n.at( 0 );
    node child_2 = children_n.at( 1 );

    bool exist = false;
    signal comune;
    ntk.foreach_fanin( child_1, [&]( signal const& f )
                       {
                         signal granchild1 = f;
                         ntk.foreach_fanin( child_2, [&]( signal const& s )
                                            {
                                              signal granchild2 = s;
                                              // il nipote comune deve stare sul critical path
                                              if ( granchild1 == granchild2 && ntk.is_on_critical_path( ntk.get_node( granchild1 ) ) )
                                              {
                                                exist = true;
                                                comune = granchild1;
                                              }
                                            } );
                       } );

    if ( !exist )
      return false;

    std::vector<signal> diversi;

    ntk.foreach_fanin( child_1, [&]( signal const& z )
                       {
                         if ( ( comune != z ) && !ntk.is_on_critical_path( ntk.get_node( z ) ) )
                           diversi.push_back( z );
                       } );

    ntk.foreach_fanin( child_2, [&]( signal const& w )
                       {
                         if ( ( comune != w ) && !ntk.is_on_critical_path( ntk.get_node( w ) ) )
                           diversi.push_back( w );
                       } );

    if ( diversi.size() == 2 ) //nessuno è un PI o non è il caso (A+B) + (A+B)
    {
      signal not_critical = ntk.create_and( diversi.at( 0 ), diversi.at( 1 ) );
      signal new_output = ntk.create_and( comune, not_critical );
      ntk.substitute_node( n, new_output );
      return true;
    }
    else
      return false;
  }
  }  

  /* ------------------------------------------------------------------------------------------------------ */


  bool try_3_layer (node n)
  {
    if ( !ntk.is_on_critical_path( n ) )
      return false;
    else
    {
      
      //analizzo figli di n --> metto a dx il ramo lungo, vedo se non critici

      std::vector<node> children_n;
      std::vector<signal> children_s;
      ntk.foreach_fanin( n, [&]( signal const& s )
                         {
                           node child = ntk.get_node( s );
                           children_n.push_back( child );
                           children_s.push_back( s );
                         } );

      if ( children_n.size() < 2 )
        return false;

      if ( ntk.level( children_n[0] ) > ntk.level( children_n[1] ) )
      {
        std::swap( children_n[0], children_n[1] ); //children[1] adesso è vecchio children 0, ossia il critico
        std::swap( children_s[0], children_s[1] ); //quindi children[1] è sempre il critico
      }
      else if ( ntk.level( children_n[0] ) == ntk.level( children_n[1] ) )
        return false;

      node child_critical = children_n[1];
      node child_not_critical = children_n[0];
      signal signal_crit_child = children_s[1];
      signal signal_not_cri_child = children_s[0];

      if ( (ntk.is_on_critical_path( child_critical ) && ntk.is_on_critical_path( child_not_critical )))
        return false;

      if ( !ntk.is_complemented( signal_crit_child ) )
        return false;

      // passo al figlio critico

      std::vector<node> granchildren_n;
      std::vector<signal> granchildren_s;
      ntk.foreach_fanin( child_critical, [&]( signal const& f )
                         {
                           node granchild = ntk.get_node( f );
                           granchildren_n.push_back( granchild );
                           granchildren_s.push_back( f );
                         } );

      if ( granchildren_n.size() < 2 )
        return false;

      if ( ntk.level( granchildren_n[0] ) > ntk.level( granchildren_n[1] ) )
      {
        std::swap( granchildren_n[0], granchildren_n[1] ); //children[1] adesso è vecchio children 0, ossia il critico
        std::swap( granchildren_s[0], granchildren_s[1] ); //quindi children[1] è sempre il critico
      }
      else if ( ntk.level( granchildren_n[0] ) == ntk.level( granchildren_n[1] ) )
        return false;

      node granchild_critical = granchildren_n[1];
      node granchild_not_critical = granchildren_n[0];
      signal signal_crit_granchild = granchildren_s[1];
      signal signal_not_cri_granchild = granchildren_s[0];

      if ( ( ntk.is_on_critical_path( granchild_critical ) && ntk.is_on_critical_path( granchild_not_critical ) ) )
        return false;

      if ( !ntk.is_complemented( signal_crit_granchild ))
        return false;

      // vedo i bisnipoti

      std::vector<node> greatchildren_n;
      std::vector<signal> greatchildren_s;
      ntk.foreach_fanin( granchild_critical, [&]( signal const& w )
                         {
                           node greatchild = ntk.get_node( w );
                           greatchildren_n.push_back( greatchild );
                           greatchildren_s.push_back( w );
                         } );

      if ( greatchildren_n.size() < 2 )
        return false;

      if ( ntk.level( greatchildren_n[0] ) > ntk.level( greatchildren_n[1] ) )
      {
        std::swap( greatchildren_n[0], greatchildren_n[1] ); //children[1] adesso è vecchio children 0, ossia il critico
        std::swap( greatchildren_s[0], greatchildren_s[1] ); //quindi children[1] è sempre il critico
      }
      else if ( ntk.level( greatchildren_n[0] ) == ntk.level( greatchildren_n[1] ) )
        return false;

      node greatchild_critical = greatchildren_n[1];
      node greatchild_not_critical = greatchildren_n[0];
      signal signal_crit_greatchild = greatchildren_s[1];
      signal signal_not_cri_greatchild = greatchildren_s[0];

     if ( ( ntk.is_on_critical_path( greatchild_critical ) && ntk.is_on_critical_path( greatchild_not_critical ) ) )
       return false;

      if ( ntk.level( greatchild_critical ) > ntk.level( child_not_critical ) )
      {
        signal a = ntk.create_and( signal_not_cri_greatchild, signal_not_cri_child );
        signal b = ntk.create_and( signal_crit_greatchild, a );
        signal c = ntk.create_and( signal_not_cri_child, !signal_not_cri_granchild ); //x3 negato?
        signal d = ntk.create_and( !b, !c );
        ntk.substitute_node( n, !d );
        return true;
      }
      else
        return false;


    }

  }




   /* ------------------------------------------------------------------------------------------------------ */





private:
  Ntk& ntk;
};

} // namespace detail

/* Entry point for users to call */
template<class Ntk>
void aig_algebraic_rewriting( Ntk& ntk )
{
  static_assert( std::is_same_v<typename Ntk::base_type, aig_network>, "Ntk is not an AIG" );

  depth_view dntk{ntk};
  detail::aig_algebraic_rewriting_impl p( dntk );
  p.run();
}

} /* namespace mockturtle */
