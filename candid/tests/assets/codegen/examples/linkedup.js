export default function({ IDL }) {
  const UserId_2 = UserId;

  const UserId = IDL.Principal;

  const Profile_2 = IDL.Record({
    'id': UserId,
    'imgUrl': IDL.Text,
    'title': IDL.Text,
    'education': IDL.Text,
    'experience': IDL.Text,
    'company': IDL.Text,
    'lastName': IDL.Text,
    'firstName': IDL.Text,
  });

  const Profile = Profile_2;

  const NewProfile_2 = IDL.Record({
    'imgUrl': IDL.Text,
    'title': IDL.Text,
    'education': IDL.Text,
    'experience': IDL.Text,
    'company': IDL.Text,
    'lastName': IDL.Text,
    'firstName': IDL.Text,
  });

  const NewProfile = NewProfile_2;

  return IDL.Service({
    'connect': IDL.Func([UserId_2], [], []),
    'create': IDL.Func([NewProfile], [], []),
    'get': IDL.Func([UserId_2], [Profile], ['query']),
    'getConnections': IDL.Func([UserId_2], [IDL.Vec(Profile)], []),
    'getOwnId': IDL.Func([], [UserId_2], ['query']),
    'healthcheck': IDL.Func([], [IDL.Bool], []),
    'isConnected': IDL.Func([UserId_2], [IDL.Bool], []),
    'search': IDL.Func([IDL.Text], [IDL.Vec(Profile)], ['query']),
    'update': IDL.Func([Profile], [], []),
  });
}
