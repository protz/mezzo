setlocal efm=
      \%AMezzo\ internal\ error:\ %m,
      \%EFatal\ error:\ %m,
      \%EError:\ %m,
      \%ERaised\ at\ file\ \"%f\"\\,\ line\ %l\\,\ characters\ %c-%*\\d,
      \%ECalled\ from\ file\ \"%f\"\\,\ line\ %l\\,\ characters\ %c-%*\\d,
      \%EFile\ \"%f\"\\,\ line\ %l\\,\ characters\ %c-%*\\d:,
      \%EFile\ \"%f\"\\,\ line\ %l\\,\ character\ %c:%m,
      \%+EReference\ to\ unbound\ regexp\ name\ %m,
      \%Eocamlyacc:\ e\ -\ line\ %l\ of\ \"%f\"\\,\ %m,
      \%Wocamlyacc:\ w\ -\ %m,
      \%-Zmake%.%#,
      \%C%m,
      \%D%*\\a[%*\\d]:\ Entering\ directory\ `%f',
      \%X%*\\a[%*\\d]:\ Leaving\ directory\ `%f',
      \%D%*\\a:\ Entering\ directory\ `%f',
      \%X%*\\a:\ Leaving\ directory\ `%f',
      \%DMaking\ %*\\a\ in\ %f

